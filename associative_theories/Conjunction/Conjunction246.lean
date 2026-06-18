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
import associative_theories.ImplicationsAT

open EQIndex
open ATIndex
open Conjectures

set_option maxHeartbeats 1000000


def conj246 : EQIndex → ATIndex
| eq1 => at246
| eq2 => at2
| eq3 => at52
| eq4 => at2
| eq5 => at5
| eq8 => at123
| eq10 => at5
| eq11 => at9
| eq14 => at9
| eq16 => at10
| eq38 => at2
| eq39 => at5
| eq40 => at9
| eq41 => at2
| eq43 => at55
| eq47 => at52
| eq56 => at2
| eq66 => at2
| eq75 => at5
| eq307 => at52
| eq308 => at2
| eq309 => at5
| eq310 => at2
| eq311 => at2
| eq312 => at5
| eq313 => at2
| eq314 => at2
| eq315 => at5
| eq316 => at2
| eq318 => at5
| eq323 => at52
| eq325 => at16
| eq326 => at52
| eq327 => at2
| eq329 => at5
| eq332 => at16
| eq333 => at52
| eq343 => at5
| eq411 => at246
| eq419 => at10
| eq429 => at10
| eq440 => at59
| eq477 => at59
| eq504 => at59
| eq513 => at247
| eq3253 => at123
| eq3255 => at5
| eq3256 => at9
| eq3258 => at5
| eq3259 => at9
| eq3260 => at2
| eq3261 => at10
| eq3264 => at5
| eq3265 => at2
| eq3267 => at2
| eq3271 => at10
| eq3273 => at2
| eq3274 => at5
| eq3275 => at2
| eq3277 => at2
| eq3278 => at10
| eq3290 => at2
| eq3292 => at5
| eq3300 => at5
| eq3306 => at123
| eq3308 => at17
| eq3309 => at52
| eq3315 => at17
| eq3316 => at52
| eq3319 => at123
| eq3322 => at5
| eq3323 => at9
| eq3326 => at5
| eq3331 => at9
| eq3334 => at10
| eq3342 => at17
| eq3346 => at123
| eq3350 => at9
| eq3353 => at123
| eq3388 => at10
| eq3414 => at10
| eq4268 => at2
| eq4269 => at5
| eq4270 => at9
| eq4271 => at2
| eq4272 => at5
| eq4273 => at9
| eq4274 => at2
| eq4275 => at10
| eq4276 => at2
| eq4277 => at2
| eq4278 => at5
| eq4279 => at2
| eq4280 => at2
| eq4283 => at55
| eq4284 => at52
| eq4286 => at2
| eq4287 => at5
| eq4288 => at2
| eq4290 => at55
| eq4291 => at52
| eq4293 => at16
| eq4296 => at5
| eq4297 => at9
| eq4299 => at2
| eq4300 => at5
| eq4301 => at2
| eq4304 => at5
| eq4305 => at9
| eq4314 => at16
| eq4315 => at2
| eq4318 => at2
| eq4320 => at246
| eq4321 => at16
| eq4325 => at9
| eq4327 => at5
| eq4331 => at2
| eq4343 => at16
| eq4358 => at55
| eq4362 => at361
| eq4364 => at55
| eq4369 => at55
| eq4512 => at246


private theorem AT246_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation1 G)) : AssociativeTheory246 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT246_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h47 := Equation4_4512_implies_Equation47 G h4 h4512
  have h4270 := Equation4_4512_implies_Equation4270 G h4 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation5 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h5, h4512⟩

private theorem AT246_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation8 G)) : AssociativeTheory123 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  exact ⟨h8, h3346, h4512⟩

private theorem AT246_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation10 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h323 := Equation10_4512_implies_Equation323 G h10 h4512
  have h4284 := Equation10_4512_implies_Equation4284 G h10 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation11 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3319 := Equation11_4512_implies_Equation3319 G h11 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation14 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h14, h4512⟩

private theorem AT246_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation16 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h16, h4512⟩

private theorem AT246_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation38 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation38_4512_implies_Equation4268 G h38 h4512
  have h4270 := Equation38_4512_implies_Equation4270 G h38 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation39 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h333 := Equation39_4512_implies_Equation333 G h39 h4512
  have h3261 := Equation39_4512_implies_Equation3261 G h39 h4512
  have h4269 := Equation39_4512_implies_Equation4269 G h39 h4512
  have h4275 := Equation39_4512_implies_Equation4275 G h39 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation40 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h4270 := Equation40_4512_implies_Equation4270 G h40 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4283 := Equation4290_4320_4512_implies_Equation4283 G h4290 h4320 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
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

private theorem AT246_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation41 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation41_4512_implies_Equation4276 G h41 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation43 G)) : AssociativeTheory55 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h43, h411, h4512⟩

private theorem AT246_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation47 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation56 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation56_4320_4512_implies_Equation43 G h56 h4320 h4512
  have h66 := Equation43_56_4512_implies_Equation66 G h43 h56 h4512
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation75 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h5 := Equation3_75_4512_implies_Equation5 G h3 h75 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation307 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h307⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation307_4512_implies_Equation3253 G h307 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3309 := Equation323_326_4512_implies_Equation3309 G h323 h326 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation308 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h309 := Equation3255_4320_4512_implies_Equation309 G h3255 h4320 h4512
  have h40 := Equation3256_4320_4512_implies_Equation40 G h3256 h4320 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation309 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation309_4512_implies_Equation3253 G h309 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation310 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation310_4512_implies_Equation4268 G h310 h4512
  have h4270 := Equation310_4512_implies_Equation4270 G h310 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation311 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation311_4512_implies_Equation4268 G h311 h4512
  have h4270 := Equation311_4512_implies_Equation4270 G h311 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation312 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h307 := Equation312_4512_implies_Equation307 G h312 h4512
  have h3253 := Equation312_4512_implies_Equation3253 G h312 h4512
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h4272 := Equation312_4512_implies_Equation4272 G h312 h4512
  have h3261 := Equation3278_4320_4512_implies_Equation3261 G h3278 h4320 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation313 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation313_4512_implies_Equation4276 G h313 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation314 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation314_4512_implies_Equation4276 G h314 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation315 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation315_4512_implies_Equation3261 G h315 h4512
  have h4272 := Equation315_4512_implies_Equation4272 G h315 h4512
  have h4275 := Equation315_4512_implies_Equation4275 G h315 h4512
  have h4284 := Equation315_4512_implies_Equation4284 G h315 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation316 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation316_4512_implies_Equation4276 G h316 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation318 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation318_4512_implies_Equation3261 G h318 h4512
  have h4275 := Equation318_4512_implies_Equation4275 G h318 h4512
  have h4291 := Equation318_4512_implies_Equation4291 G h318 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation323 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h307 := Equation323_4512_implies_Equation307 G h323 h4512
  have h3253 := Equation323_4512_implies_Equation3253 G h323 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3309 := Equation323_326_4512_implies_Equation3309 G h323 h326 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation325 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h326 := Equation325_4512_implies_Equation326 G h325 h4512
  have h4314 := Equation325_4512_implies_Equation4314 G h325 h4512
  have h4343 := Equation4314_4320_4512_implies_Equation4343 G h4314 h4320 h4512
  have h3 := Equation411_4314_4512_implies_Equation3 G h411 h4314 h4512
  have h43 := Equation326_4343_4512_implies_Equation43 G h326 h4343 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT246_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation326 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h307 := Equation326_4512_implies_Equation307 G h326 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h4291 := Equation333_4512_implies_Equation4291 G h333 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation327 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3256 := Equation327_4512_implies_Equation3256 G h327 h4512
  have h4268 := Equation327_4512_implies_Equation4268 G h327 h4512
  have h4314 := Equation327_4512_implies_Equation4314 G h327 h4512
  have h4315 := Equation327_4512_implies_Equation4315 G h327 h4512
  have h3 := Equation411_4314_4512_implies_Equation3 G h411 h4314 h4512
  have h4275 := Equation4268_4320_4512_implies_Equation4275 G h4268 h4320 h4512
  have h40 := Equation3256_4320_4512_implies_Equation40 G h3256 h4320 h4512
  have h4269 := Equation4275_4315_4512_implies_Equation4269 G h4275 h4315 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation329 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h323 := Equation329_4512_implies_Equation323 G h329 h4512
  have h3253 := Equation329_4512_implies_Equation3253 G h329 h4512
  have h3261 := Equation329_4512_implies_Equation3261 G h329 h4512
  have h4269 := Equation329_4512_implies_Equation4269 G h329 h4512
  have h4284 := Equation329_4512_implies_Equation4284 G h329 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation332 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation332_4512_implies_Equation43 G h332 h4512
  have h4284 := Equation332_4512_implies_Equation4284 G h332 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT246_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation333 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4291 := Equation333_4512_implies_Equation4291 G h333 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation343 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h333 := Equation343_4512_implies_Equation333 G h343 h4512
  have h3253 := Equation343_4512_implies_Equation3253 G h343 h4512
  have h3278 := Equation343_4512_implies_Equation3278 G h343 h4512
  have h4291 := Equation343_4512_implies_Equation4291 G h343 h4512
  have h3261 := Equation3278_4320_4512_implies_Equation3261 G h3278 h4320 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation411 G)) : AssociativeTheory246 G := by
  obtain ⟨hh, h411⟩ := h
  exact hh

private theorem AT246_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation419 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3319 := Equation419_4512_implies_Equation3319 G h419 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation429 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3319 := Equation429_4512_implies_Equation3319 G h429 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation440 G)) : AssociativeTheory59 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation440_4320_4512_implies_Equation43 G h440 h4320 h4512
  exact ⟨h43, h440, h4512⟩

private theorem AT246_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation477 G)) : AssociativeTheory59 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation477_4512_implies_Equation43 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  exact ⟨h43, h440, h4512⟩

private theorem AT246_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation504 G)) : AssociativeTheory59 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h43 := Equation440_4320_4512_implies_Equation43 G h440 h4320 h4512
  exact ⟨h43, h440, h4512⟩

private theorem AT246_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation513 G)) : AssociativeTheory247 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h513, h4320, h4512⟩

private theorem AT246_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3253 G)) : AssociativeTheory123 G := by
  obtain ⟨hh, h3253⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  exact ⟨h8, h3346, h4512⟩

private theorem AT246_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3255 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h309 := Equation3255_4320_4512_implies_Equation309 G h3255 h4320 h4512
  have h307 := Equation3255_4512_implies_Equation307 G h3255 h4512
  have h3253 := Equation3255_4512_implies_Equation3253 G h3255 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3256 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h40 := Equation3256_4320_4512_implies_Equation40 G h3256 h4320 h4512
  have h3253 := Equation3256_4512_implies_Equation3253 G h3256 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4283 := Equation4290_4320_4512_implies_Equation4283 G h4290 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  have h3342 := Equation43_3306_4512_implies_Equation3342 G h43 h3306 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h3353 := Equation3342_4512_implies_Equation3353 G h3342 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3258 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h309 := Equation3258_4320_4512_implies_Equation309 G h3258 h4320 h4512
  have h307 := Equation3258_4512_implies_Equation307 G h3258 h4512
  have h3253 := Equation3258_4512_implies_Equation3253 G h3258 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3259 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h4270 := Equation3259_4512_implies_Equation4270 G h3259 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3260 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation3260_4512_implies_Equation4268 G h3260 h4512
  have h4270 := Equation3260_4512_implies_Equation4270 G h3260 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3261 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3261_4512_implies_Equation3253 G h3261 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3264 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3264_4512_implies_Equation3253 G h3264 h4512
  have h3261 := Equation3264_4512_implies_Equation3261 G h3264 h4512
  have h4284 := Equation3264_4512_implies_Equation4284 G h3264 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3265 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation3265_4512_implies_Equation4268 G h3265 h4512
  have h4270 := Equation3265_4512_implies_Equation4270 G h3265 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3267 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation3267_4512_implies_Equation4268 G h3267 h4512
  have h4270 := Equation3267_4512_implies_Equation4270 G h3267 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3271 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h4275 := Equation3271_4512_implies_Equation4275 G h3271 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation3273_4512_implies_Equation4276 G h3273 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3274 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3274_4512_implies_Equation3261 G h3274 h4512
  have h4272 := Equation3274_4512_implies_Equation4272 G h3274 h4512
  have h4275 := Equation3274_4512_implies_Equation4275 G h3274 h4512
  have h4284 := Equation3274_4512_implies_Equation4284 G h3274 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3275 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation3275_4512_implies_Equation4276 G h3275 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation3277_4512_implies_Equation4276 G h3277 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3278 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3278_4320_4512_implies_Equation3261 G h3278 h4320 h4512
  have h3253 := Equation3278_4512_implies_Equation3253 G h3278 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3290 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation3290_4512_implies_Equation4276 G h3290 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3292 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3292_4512_implies_Equation3261 G h3292 h4512
  have h4272 := Equation3292_4512_implies_Equation4272 G h3292 h4512
  have h4275 := Equation3292_4512_implies_Equation4275 G h3292 h4512
  have h4284 := Equation3292_4512_implies_Equation4284 G h3292 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3300 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3300_4512_implies_Equation3261 G h3300 h4512
  have h4272 := Equation3300_4512_implies_Equation4272 G h3300 h4512
  have h4275 := Equation3300_4512_implies_Equation4275 G h3300 h4512
  have h4284 := Equation3300_4512_implies_Equation4284 G h3300 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3306 G)) : AssociativeTheory123 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3306_4512_implies_Equation3253 G h3306 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  exact ⟨h8, h3346, h4512⟩

private theorem AT246_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3308 G)) : AssociativeTheory17 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3308_4512_implies_Equation3253 G h3308 h4512
  have h4283 := Equation3308_4512_implies_Equation4283 G h3308 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  exact ⟨h8, h43, h4512⟩

private theorem AT246_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3309 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h323 := Equation3309_4512_implies_Equation323 G h3309 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3315 G)) : AssociativeTheory17 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3315_4512_implies_Equation3253 G h3315 h4512
  have h3319 := Equation3315_4512_implies_Equation3319 G h3315 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h43 := Equation3315_3353_4512_implies_Equation43 G h3315 h3353 h4512
  exact ⟨h8, h43, h4512⟩

private theorem AT246_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3316 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h3316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h307 := Equation3316_4512_implies_Equation307 G h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h4291 := Equation333_4512_implies_Equation4291 G h333 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3319 G)) : AssociativeTheory123 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3253 := Equation3319_4512_implies_Equation3253 G h3319 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  exact ⟨h8, h3346, h4512⟩

private theorem AT246_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3322 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h307 := Equation3322_4512_implies_Equation307 G h3322 h4512
  have h3253 := Equation3322_4512_implies_Equation3253 G h3322 h4512
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  have h3319 := Equation3322_4512_implies_Equation3319 G h3322 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h309 := Equation3255_4320_4512_implies_Equation309 G h3255 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3323 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3323_4512_implies_Equation3253 G h3323 h4512
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  have h3319 := Equation3323_4512_implies_Equation3319 G h3323 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h40 := Equation3256_4320_4512_implies_Equation40 G h3256 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3326 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h323 := Equation3326_4512_implies_Equation323 G h3326 h4512
  have h3253 := Equation3326_4512_implies_Equation3253 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  have h309 := Equation3258_4320_4512_implies_Equation309 G h3258 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3331 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h3319 := Equation3331_4512_implies_Equation3319 G h3331 h4512
  have h4270 := Equation3331_4512_implies_Equation4270 G h3331 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3334 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3334_4512_implies_Equation3253 G h3334 h4512
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h3319 := Equation3334_4512_implies_Equation3319 G h3334 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3342 G)) : AssociativeTheory17 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation3342_4512_implies_Equation43 G h3342 h4512
  have h3253 := Equation3342_4512_implies_Equation3253 G h3342 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  exact ⟨h8, h43, h4512⟩

private theorem AT246_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3346 G)) : AssociativeTheory123 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3346_4512_implies_Equation3253 G h3346 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  exact ⟨h8, h3346, h4512⟩

private theorem AT246_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3350 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3350_4512_implies_Equation3261 G h3350 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h3353 := Equation3350_4512_implies_Equation3353 G h3350 h4512
  have h4270 := Equation3350_4512_implies_Equation4270 G h3350 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3353 G)) : AssociativeTheory123 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3319 := Equation3353_4320_4512_implies_Equation3319 G h3353 h4320 h4512
  have h3253 := Equation3353_4512_implies_Equation3253 G h3353 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  exact ⟨h8, h3346, h4512⟩

private theorem AT246_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3388 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3261 := Equation3388_4512_implies_Equation3261 G h3388 h4512
  have h3353 := Equation3388_4512_implies_Equation3353 G h3388 h4512
  have h4275 := Equation3388_4512_implies_Equation4275 G h3388 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation3414 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3253 := Equation3414_4512_implies_Equation3253 G h3414 h4512
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h3353 := Equation3414_4512_implies_Equation3353 G h3414 h4512
  have h3261 := Equation3278_4320_4512_implies_Equation3261 G h3278 h4320 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4268 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4275 := Equation4268_4320_4512_implies_Equation4275 G h4268 h4320 h4512
  have h4277 := Equation4268_4275_4512_implies_Equation4277 G h4268 h4275 h4512
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4269 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4270 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4271 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4270 := Equation4271_4512_implies_Equation4270 G h4271 h4512
  have h4314 := Equation4271_4512_implies_Equation4314 G h4271 h4512
  have h3 := Equation411_4314_4512_implies_Equation3 G h411 h4314 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4272 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4269 := Equation4272_4320_4512_implies_Equation4269 G h4272 h4320 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4273 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h8 := Equation411_4273_4512_implies_Equation8 G h411 h4273 h4512
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4274 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4274_4512_implies_Equation4276 G h4274 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4275 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h16 := Equation429_3353_4512_implies_Equation16 G h429 h3353 h4512
  exact ⟨h16, h4512⟩

private theorem AT246_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4276 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4278 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4269 := Equation4278_4512_implies_Equation4269 G h4278 h4512
  have h4275 := Equation4278_4512_implies_Equation4275 G h4278 h4512
  have h4291 := Equation4278_4512_implies_Equation4291 G h4278 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4279 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4279_4512_implies_Equation4276 G h4279 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4280 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4280_4512_implies_Equation4276 G h4280 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4283 G)) : AssociativeTheory55 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  exact ⟨h43, h411, h4512⟩

private theorem AT246_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4284 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4286 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h4283 := Equation4286_4512_implies_Equation4283 G h4286 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4287 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4269 := Equation4287_4512_implies_Equation4269 G h4287 h4512
  have h4284 := Equation4287_4512_implies_Equation4284 G h4287 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4288 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4270 := Equation4288_4512_implies_Equation4270 G h4288 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h3 := Equation411_4268_4512_implies_Equation3 G h411 h4268 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4290 G)) : AssociativeTheory55 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4283 := Equation4290_4320_4512_implies_Equation4283 G h4290 h4320 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  exact ⟨h43, h411, h4512⟩

private theorem AT246_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4291 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT246_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4293 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3 := Equation411_4293_4512_implies_Equation3 G h411 h4293 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT246_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4296 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  have h4291 := Equation4296_4512_implies_Equation4291 G h4296 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4297 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4270 := Equation4297_4512_implies_Equation4270 G h4297 h4512
  have h4275 := Equation4297_4512_implies_Equation4275 G h4297 h4512
  have h4290 := Equation4297_4512_implies_Equation4290 G h4297 h4512
  have h4283 := Equation4290_4320_4512_implies_Equation4283 G h4290 h4320 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3342 := Equation43_3306_4512_implies_Equation3342 G h43 h3306 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3315 := Equation3342_4512_implies_Equation3315 G h3342 h4512
  have h3353 := Equation3342_4512_implies_Equation3353 G h3342 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4299 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4299_4512_implies_Equation4276 G h4299 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4300 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4272 := Equation4300_4512_implies_Equation4272 G h4300 h4512
  have h4291 := Equation4300_4512_implies_Equation4291 G h4300 h4512
  have h4269 := Equation4272_4320_4512_implies_Equation4269 G h4272 h4320 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4301 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4301_4512_implies_Equation4276 G h4301 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4304 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h4275 := Equation4304_4512_implies_Equation4275 G h4304 h4512
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation411_4275_4512_implies_Equation8 G h411 h4275 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4305 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h4275 := Equation4305_4512_implies_Equation4275 G h4305 h4512
  have h4283 := Equation4305_4512_implies_Equation4283 G h4305 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h8 := Equation411_4273_4512_implies_Equation8 G h411 h4273 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3342 := Equation43_3306_4512_implies_Equation3342 G h43 h3306 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3315 := Equation3342_4512_implies_Equation3315 G h3342 h4512
  have h3353 := Equation3342_4512_implies_Equation3353 G h3342 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4314 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4321 := Equation4314_4320_4512_implies_Equation4321 G h4314 h4320 h4512
  have h3 := Equation411_4314_4512_implies_Equation3 G h411 h4314 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4293 := Equation307_4284_4321_4512_implies_Equation4293 G h307 h4284 h4321 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT246_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4315 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4268 := Equation4315_4512_implies_Equation4268 G h4315 h4512
  have h4275 := Equation4268_4320_4512_implies_Equation4275 G h4268 h4320 h4512
  have h4277 := Equation4268_4275_4512_implies_Equation4277 G h4268 h4275 h4512
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4318 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4270 := Equation4318_4512_implies_Equation4270 G h4318 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h3 := Equation411_4269_4512_implies_Equation3 G h411 h4269 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4320 G)) : AssociativeTheory246 G := by
  obtain ⟨hh, h4320⟩ := h
  exact hh

private theorem AT246_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4321 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h3 := Equation411_4321_4512_implies_Equation3 G h411 h4321 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4293 := Equation307_4284_4321_4512_implies_Equation4293 G h307 h4284 h4321 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT246_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4325 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h8 := Equation411_4273_4512_implies_Equation8 G h411 h4273 h4512
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT246_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4327 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4272 := Equation4327_4512_implies_Equation4272 G h4327 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT246_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4331 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4276 := Equation4331_4512_implies_Equation4276 G h4331 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT246_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4343 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4314 := Equation4320_4343_4512_implies_Equation4314 G h4320 h4343 h4512
  have h3 := Equation411_4343_4512_implies_Equation3 G h411 h4343 h4512
  have h4321 := Equation4314_4320_4512_implies_Equation4321 G h4314 h4320 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4293 := Equation307_4284_4321_4512_implies_Equation4293 G h307 h4284 h4321 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT246_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4358 G)) : AssociativeTheory55 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h4283 := Equation4358_4512_implies_Equation4283 G h4358 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  exact ⟨h43, h411, h4512⟩

private theorem AT246_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4362 G)) : AssociativeTheory361 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  exact ⟨h411, h4362, h4512⟩

private theorem AT246_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4364 G)) : AssociativeTheory55 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation411_4364_4512_implies_Equation43 G h411 h4364 h4512
  exact ⟨h43, h411, h4512⟩

private theorem AT246_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4369 G)) : AssociativeTheory55 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at246
  obtain ⟨h1, h411, h4320, h4512⟩ := g hh
  have h43 := Equation411_4369_4512_implies_Equation43 G h411 h4369 h4512
  exact ⟨h43, h411, h4512⟩

private theorem AT246_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory246 G) ∧ (Equation4512 G)) : AssociativeTheory246 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT246_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj246 eqid)) : (AssociativeTheory246 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj246 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at246 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT246_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory246 G) ∧ (EQeq G eqid) <-> (ATearly G (conj246 eqid)) :=
⟨match eqid with
| eq1 => AT246_Equation1_implies G
| eq2 => AT246_Equation2_implies G
| eq3 => AT246_Equation3_implies G
| eq4 => AT246_Equation4_implies G
| eq5 => AT246_Equation5_implies G
| eq8 => AT246_Equation8_implies G
| eq10 => AT246_Equation10_implies G
| eq11 => AT246_Equation11_implies G
| eq14 => AT246_Equation14_implies G
| eq16 => AT246_Equation16_implies G
| eq38 => AT246_Equation38_implies G
| eq39 => AT246_Equation39_implies G
| eq40 => AT246_Equation40_implies G
| eq41 => AT246_Equation41_implies G
| eq43 => AT246_Equation43_implies G
| eq47 => AT246_Equation47_implies G
| eq56 => AT246_Equation56_implies G
| eq66 => AT246_Equation66_implies G
| eq75 => AT246_Equation75_implies G
| eq307 => AT246_Equation307_implies G
| eq308 => AT246_Equation308_implies G
| eq309 => AT246_Equation309_implies G
| eq310 => AT246_Equation310_implies G
| eq311 => AT246_Equation311_implies G
| eq312 => AT246_Equation312_implies G
| eq313 => AT246_Equation313_implies G
| eq314 => AT246_Equation314_implies G
| eq315 => AT246_Equation315_implies G
| eq316 => AT246_Equation316_implies G
| eq318 => AT246_Equation318_implies G
| eq323 => AT246_Equation323_implies G
| eq325 => AT246_Equation325_implies G
| eq326 => AT246_Equation326_implies G
| eq327 => AT246_Equation327_implies G
| eq329 => AT246_Equation329_implies G
| eq332 => AT246_Equation332_implies G
| eq333 => AT246_Equation333_implies G
| eq343 => AT246_Equation343_implies G
| eq411 => AT246_Equation411_implies G
| eq419 => AT246_Equation419_implies G
| eq429 => AT246_Equation429_implies G
| eq440 => AT246_Equation440_implies G
| eq477 => AT246_Equation477_implies G
| eq504 => AT246_Equation504_implies G
| eq513 => AT246_Equation513_implies G
| eq3253 => AT246_Equation3253_implies G
| eq3255 => AT246_Equation3255_implies G
| eq3256 => AT246_Equation3256_implies G
| eq3258 => AT246_Equation3258_implies G
| eq3259 => AT246_Equation3259_implies G
| eq3260 => AT246_Equation3260_implies G
| eq3261 => AT246_Equation3261_implies G
| eq3264 => AT246_Equation3264_implies G
| eq3265 => AT246_Equation3265_implies G
| eq3267 => AT246_Equation3267_implies G
| eq3271 => AT246_Equation3271_implies G
| eq3273 => AT246_Equation3273_implies G
| eq3274 => AT246_Equation3274_implies G
| eq3275 => AT246_Equation3275_implies G
| eq3277 => AT246_Equation3277_implies G
| eq3278 => AT246_Equation3278_implies G
| eq3290 => AT246_Equation3290_implies G
| eq3292 => AT246_Equation3292_implies G
| eq3300 => AT246_Equation3300_implies G
| eq3306 => AT246_Equation3306_implies G
| eq3308 => AT246_Equation3308_implies G
| eq3309 => AT246_Equation3309_implies G
| eq3315 => AT246_Equation3315_implies G
| eq3316 => AT246_Equation3316_implies G
| eq3319 => AT246_Equation3319_implies G
| eq3322 => AT246_Equation3322_implies G
| eq3323 => AT246_Equation3323_implies G
| eq3326 => AT246_Equation3326_implies G
| eq3331 => AT246_Equation3331_implies G
| eq3334 => AT246_Equation3334_implies G
| eq3342 => AT246_Equation3342_implies G
| eq3346 => AT246_Equation3346_implies G
| eq3350 => AT246_Equation3350_implies G
| eq3353 => AT246_Equation3353_implies G
| eq3388 => AT246_Equation3388_implies G
| eq3414 => AT246_Equation3414_implies G
| eq4268 => AT246_Equation4268_implies G
| eq4269 => AT246_Equation4269_implies G
| eq4270 => AT246_Equation4270_implies G
| eq4271 => AT246_Equation4271_implies G
| eq4272 => AT246_Equation4272_implies G
| eq4273 => AT246_Equation4273_implies G
| eq4274 => AT246_Equation4274_implies G
| eq4275 => AT246_Equation4275_implies G
| eq4276 => AT246_Equation4276_implies G
| eq4277 => AT246_Equation4277_implies G
| eq4278 => AT246_Equation4278_implies G
| eq4279 => AT246_Equation4279_implies G
| eq4280 => AT246_Equation4280_implies G
| eq4283 => AT246_Equation4283_implies G
| eq4284 => AT246_Equation4284_implies G
| eq4286 => AT246_Equation4286_implies G
| eq4287 => AT246_Equation4287_implies G
| eq4288 => AT246_Equation4288_implies G
| eq4290 => AT246_Equation4290_implies G
| eq4291 => AT246_Equation4291_implies G
| eq4293 => AT246_Equation4293_implies G
| eq4296 => AT246_Equation4296_implies G
| eq4297 => AT246_Equation4297_implies G
| eq4299 => AT246_Equation4299_implies G
| eq4300 => AT246_Equation4300_implies G
| eq4301 => AT246_Equation4301_implies G
| eq4304 => AT246_Equation4304_implies G
| eq4305 => AT246_Equation4305_implies G
| eq4314 => AT246_Equation4314_implies G
| eq4315 => AT246_Equation4315_implies G
| eq4318 => AT246_Equation4318_implies G
| eq4320 => AT246_Equation4320_implies G
| eq4321 => AT246_Equation4321_implies G
| eq4325 => AT246_Equation4325_implies G
| eq4327 => AT246_Equation4327_implies G
| eq4331 => AT246_Equation4331_implies G
| eq4343 => AT246_Equation4343_implies G
| eq4358 => AT246_Equation4358_implies G
| eq4362 => AT246_Equation4362_implies G
| eq4364 => AT246_Equation4364_implies G
| eq4369 => AT246_Equation4369_implies G
| eq4512 => AT246_Equation4512_implies G
, AT246_conj_implied G eqid⟩

