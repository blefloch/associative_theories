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


def conj174 : EQIndex → ATIndex
| eq1 => at174
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
| eq40 => at26
| eq41 => at13
| eq43 => at175
| eq47 => at3
| eq56 => at4
| eq66 => at2
| eq75 => at5
| eq307 => at176
| eq308 => at33
| eq309 => at30
| eq310 => at33
| eq311 => at34
| eq312 => at39
| eq313 => at31
| eq314 => at35
| eq315 => at39
| eq316 => at26
| eq318 => at40
| eq323 => at50
| eq325 => at48
| eq326 => at50
| eq327 => at11
| eq329 => at43
| eq332 => at42
| eq333 => at53
| eq343 => at12
| eq411 => at3
| eq419 => at7
| eq429 => at7
| eq440 => at4
| eq477 => at2
| eq504 => at2
| eq513 => at5
| eq3253 => at176
| eq3255 => at70
| eq3256 => at33
| eq3258 => at70
| eq3259 => at33
| eq3260 => at72
| eq3261 => at70
| eq3264 => at75
| eq3265 => at81
| eq3267 => at89
| eq3271 => at39
| eq3273 => at73
| eq3274 => at95
| eq3275 => at76
| eq3277 => at90
| eq3278 => at39
| eq3290 => at82
| eq3292 => at98
| eq3300 => at102
| eq3306 => at50
| eq3308 => at48
| eq3309 => at50
| eq3315 => at48
| eq3316 => at50
| eq3319 => at50
| eq3322 => at43
| eq3323 => at11
| eq3326 => at43
| eq3331 => at11
| eq3334 => at43
| eq3342 => at42
| eq3346 => at53
| eq3350 => at13
| eq3353 => at53
| eq3388 => at12
| eq3414 => at12
| eq4268 => at133
| eq4269 => at178
| eq4270 => at133
| eq4271 => at136
| eq4272 => at154
| eq4273 => at179
| eq4274 => at144
| eq4275 => at154
| eq4276 => at180
| eq4277 => at139
| eq4278 => at160
| eq4279 => at179
| eq4280 => at139
| eq4283 => at182
| eq4284 => at174
| eq4286 => at135
| eq4287 => at185
| eq4288 => at133
| eq4290 => at198
| eq4291 => at217
| eq4293 => at198
| eq4296 => at155
| eq4297 => at139
| eq4299 => at139
| eq4300 => at160
| eq4301 => at141
| eq4304 => at154
| eq4305 => at141
| eq4314 => at182
| eq4315 => at136
| eq4318 => at135
| eq4320 => at217
| eq4321 => at274
| eq4325 => at141
| eq4327 => at155
| eq4331 => at141
| eq4343 => at198
| eq4358 => at332
| eq4362 => at381
| eq4364 => at417
| eq4369 => at440
| eq4512 => at174


private theorem AT174_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation1 G)) : AssociativeTheory174 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT174_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT174_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3, h4512⟩

private theorem AT174_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4, h4512⟩

private theorem AT174_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation5 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h5, h4512⟩

private theorem AT174_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation8 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation8_4512_implies_Equation411 G h8 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h4512⟩

private theorem AT174_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation10 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h10, h4512⟩

private theorem AT174_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation11 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation11_4512_implies_Equation411 G h11 h4512
  have h429 := Equation11_4512_implies_Equation429 G h11 h4512
  have h3253 := Equation11_4512_implies_Equation3253 G h11 h4512
  have h3315 := Equation11_4512_implies_Equation3315 G h11 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT174_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation14_4512_implies_Equation411 G h14 h4512
  have h4273 := Equation14_4512_implies_Equation4273 G h14 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT174_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation16 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation16_4512_implies_Equation411 G h16 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3253 := Equation16_4512_implies_Equation3253 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT174_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation38 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h38, h4512⟩

private theorem AT174_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation39 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h39, h4512⟩

private theorem AT174_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation40 G)) : AssociativeTheory26 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation40_4512_implies_Equation3253 G h40 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  exact ⟨h40, h307, h4512⟩

private theorem AT174_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h38 := Equation41_4512_implies_Equation38 G h41 h4512
  have h39 := Equation41_4512_implies_Equation39 G h41 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT174_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation43 G)) : AssociativeTheory175 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h43, h4284, h4512⟩

private theorem AT174_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation47 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  exact ⟨h3, h4512⟩

private theorem AT174_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation56 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h47 := Equation56_4512_implies_Equation47 G h56 h4512
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  have h4 := Equation3_56_4512_implies_Equation4 G h3 h56 h4512
  exact ⟨h4, h4512⟩

private theorem AT174_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h47 := Equation66_4512_implies_Equation47 G h66 h4512
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT174_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation75 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  have h5 := Equation3_75_4512_implies_Equation5 G h3 h75 h4512
  exact ⟨h5, h4512⟩

private theorem AT174_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation307 G)) : AssociativeTheory176 G := by
  obtain ⟨hh, h307⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h307, h4284, h4512⟩

private theorem AT174_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation308 G)) : AssociativeTheory33 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h310 := Equation308_4284_4512_implies_Equation310 G h308 h4284 h4512
  exact ⟨h310, h4512⟩

private theorem AT174_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation309 G)) : AssociativeTheory30 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h309, h4512⟩

private theorem AT174_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation310 G)) : AssociativeTheory33 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h310, h4512⟩

private theorem AT174_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation311 G)) : AssociativeTheory34 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h311, h4512⟩

private theorem AT174_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation312 G)) : AssociativeTheory39 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  exact ⟨h315, h4512⟩

private theorem AT174_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation313 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation313_4512_implies_Equation40 G h313 h4512
  have h309 := Equation313_4512_implies_Equation309 G h313 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT174_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation314 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation314_4512_implies_Equation40 G h314 h4512
  have h311 := Equation314_4512_implies_Equation311 G h314 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT174_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation315 G)) : AssociativeTheory39 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h315, h4512⟩

private theorem AT174_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation316 G)) : AssociativeTheory26 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation316_4512_implies_Equation40 G h316 h4512
  have h307 := Equation316_4512_implies_Equation307 G h316 h4512
  exact ⟨h40, h307, h4512⟩

private theorem AT174_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation318 G)) : AssociativeTheory40 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h318, h4512⟩

private theorem AT174_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation323 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT174_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation325 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h326 := Equation325_4512_implies_Equation326 G h325 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT174_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation326 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT174_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation327 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  have h3255 := Equation327_4512_implies_Equation3255 G h327 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT174_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation329 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h309 := Equation329_4512_implies_Equation309 G h329 h4512
  have h323 := Equation329_4512_implies_Equation323 G h329 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT174_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation332 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h43 := Equation332_4512_implies_Equation43 G h332 h4512
  have h323 := Equation332_4512_implies_Equation323 G h332 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT174_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation333 G)) : AssociativeTheory53 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h323 := Equation333_4512_implies_Equation323 G h333 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  exact ⟨h326, h333, h4512⟩

private theorem AT174_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation343 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h312 := Equation343_4512_implies_Equation312 G h343 h4512
  have h323 := Equation343_4512_implies_Equation323 G h343 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT174_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation411 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h4512⟩

private theorem AT174_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation419 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation419_4512_implies_Equation411 G h419 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT174_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation429 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation429_4512_implies_Equation411 G h429 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT174_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation440 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h429 := Equation11_4512_implies_Equation429 G h11 h4512
  have h3315 := Equation11_4512_implies_Equation3315 G h11 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT174_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  have h4320 := Equation477_4512_implies_Equation4320 G h477 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT174_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h513 := Equation504_4512_implies_Equation513 G h504 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4320 := Equation16_4512_implies_Equation4320 G h16 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT174_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation513 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT174_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3253 G)) : AssociativeTheory176 G := by
  obtain ⟨hh, h3253⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  exact ⟨h307, h4284, h4512⟩

private theorem AT174_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3255 G)) : AssociativeTheory70 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  exact ⟨h3255, h3258, h4512⟩

private theorem AT174_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3256 G)) : AssociativeTheory33 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3256_4512_implies_Equation3253 G h3256 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h308 := Equation307_3256_4512_implies_Equation308 G h307 h3256 h4512
  have h310 := Equation308_4284_4512_implies_Equation310 G h308 h4284 h4512
  exact ⟨h310, h4512⟩

private theorem AT174_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3258 G)) : AssociativeTheory70 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3255 := Equation3258_4284_4512_implies_Equation3255 G h3258 h4284 h4512
  exact ⟨h3255, h3258, h4512⟩

private theorem AT174_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3259 G)) : AssociativeTheory33 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3259_4512_implies_Equation3253 G h3259 h4512
  have h4270 := Equation3259_4512_implies_Equation4270 G h3259 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h310 := Equation308_4284_4512_implies_Equation310 G h308 h4284 h4512
  exact ⟨h310, h4512⟩

private theorem AT174_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3260 G)) : AssociativeTheory72 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3260, h4512⟩

private theorem AT174_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3261 G)) : AssociativeTheory70 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3261_4512_implies_Equation3253 G h3261 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h3255 := Equation3258_4284_4512_implies_Equation3255 G h3258 h4284 h4512
  exact ⟨h3255, h3258, h4512⟩

private theorem AT174_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3264 G)) : AssociativeTheory75 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3264, h4512⟩

private theorem AT174_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3265 G)) : AssociativeTheory81 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3265, h4512⟩

private theorem AT174_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3267 G)) : AssociativeTheory89 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3267, h4512⟩

private theorem AT174_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3271 G)) : AssociativeTheory39 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3271_4512_implies_Equation3253 G h3271 h4512
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  exact ⟨h315, h4512⟩

private theorem AT174_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3273 G)) : AssociativeTheory73 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation3273_4512_implies_Equation40 G h3273 h4512
  have h3260 := Equation3273_4512_implies_Equation3260 G h3273 h4512
  exact ⟨h40, h3260, h4512⟩

private theorem AT174_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3274 G)) : AssociativeTheory95 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3274, h4512⟩

private theorem AT174_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3275 G)) : AssociativeTheory76 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation3275_4512_implies_Equation40 G h3275 h4512
  have h3264 := Equation3275_4512_implies_Equation3264 G h3275 h4512
  exact ⟨h40, h3264, h4512⟩

private theorem AT174_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3277 G)) : AssociativeTheory90 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation3277_4512_implies_Equation40 G h3277 h4512
  have h3267 := Equation3277_4512_implies_Equation3267 G h3277 h4512
  exact ⟨h40, h3267, h4512⟩

private theorem AT174_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3278 G)) : AssociativeTheory39 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3278_4512_implies_Equation3253 G h3278 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  exact ⟨h315, h4512⟩

private theorem AT174_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3290 G)) : AssociativeTheory82 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h40 := Equation3290_4512_implies_Equation40 G h3290 h4512
  have h3265 := Equation3290_4512_implies_Equation3265 G h3290 h4512
  exact ⟨h40, h3265, h4512⟩

private theorem AT174_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3292 G)) : AssociativeTheory98 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3292, h4512⟩

private theorem AT174_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3300 G)) : AssociativeTheory102 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h3300, h4512⟩

private theorem AT174_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3306 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3306_4512_implies_Equation3253 G h3306 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT174_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3308 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3308_4512_implies_Equation3253 G h3308 h4512
  have h3306 := Equation3308_4512_implies_Equation3306 G h3308 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT174_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3309 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h323 := Equation3309_4512_implies_Equation323 G h3309 h4512
  have h326 := Equation3309_4512_implies_Equation326 G h3309 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT174_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3315 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3315_4512_implies_Equation3253 G h3315 h4512
  have h3319 := Equation3315_4512_implies_Equation3319 G h3315 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT174_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3316 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h3316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT174_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3319 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3319_4512_implies_Equation3253 G h3319 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT174_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3322 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h326 := Equation3322_4512_implies_Equation326 G h3322 h4512
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  have h309 := Equation323_3255_4512_implies_Equation309 G h323 h3255 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT174_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3323 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3323_4512_implies_Equation3253 G h3323 h4512
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h308 := Equation307_3256_4512_implies_Equation308 G h307 h3256 h4512
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT174_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3326 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h323 := Equation3326_4512_implies_Equation323 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  have h3255 := Equation3258_4284_4512_implies_Equation3255 G h3258 h4284 h4512
  have h309 := Equation323_3255_4512_implies_Equation309 G h323 h3255 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT174_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3331 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3331_4512_implies_Equation3253 G h3331 h4512
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT174_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3334 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3334_4512_implies_Equation3253 G h3334 h4512
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h3306 := Equation3334_4512_implies_Equation3306 G h3334 h4512
  have h3319 := Equation3334_4512_implies_Equation3319 G h3334 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h309 := Equation326_3258_4512_implies_Equation309 G h326 h3258 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT174_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3342 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h43 := Equation3342_4512_implies_Equation43 G h3342 h4512
  have h3253 := Equation3342_4512_implies_Equation3253 G h3342 h4512
  have h3306 := Equation3342_4512_implies_Equation3306 G h3342 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT174_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3346 G)) : AssociativeTheory53 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3346_4512_implies_Equation3253 G h3346 h4512
  have h3319 := Equation3346_4512_implies_Equation3319 G h3346 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  exact ⟨h326, h333, h4512⟩

private theorem AT174_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3350 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3350_4512_implies_Equation3253 G h3350 h4512
  have h3261 := Equation3350_4512_implies_Equation3261 G h3350 h4512
  have h3306 := Equation3350_4512_implies_Equation3306 G h3350 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h4275 := Equation3350_4512_implies_Equation4275 G h3350 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT174_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3353 G)) : AssociativeTheory53 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3353_4512_implies_Equation3253 G h3353 h4512
  have h3306 := Equation3353_4512_implies_Equation3306 G h3353 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  exact ⟨h326, h333, h4512⟩

private theorem AT174_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3388 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3388_4512_implies_Equation3253 G h3388 h4512
  have h3278 := Equation3388_4512_implies_Equation3278 G h3388 h4512
  have h3306 := Equation3388_4512_implies_Equation3306 G h3388 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT174_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation3414 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h3253 := Equation3414_4512_implies_Equation3253 G h3414 h4512
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h3306 := Equation3414_4512_implies_Equation3306 G h3414 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT174_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4268 G)) : AssociativeTheory133 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4270 := Equation4268_4284_4512_implies_Equation4270 G h4268 h4284 h4512
  exact ⟨h4268, h4270, h4512⟩

private theorem AT174_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4269 G)) : AssociativeTheory178 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4269, h4284, h4512⟩

private theorem AT174_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4270 G)) : AssociativeTheory133 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  exact ⟨h4268, h4270, h4512⟩

private theorem AT174_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4271 G)) : AssociativeTheory136 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4271, h4512⟩

private theorem AT174_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4272 G)) : AssociativeTheory154 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4275 := Equation4272_4284_4512_implies_Equation4275 G h4272 h4284 h4512
  exact ⟨h4272, h4275, h4512⟩

private theorem AT174_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4273 G)) : AssociativeTheory179 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4273, h4284, h4512⟩

private theorem AT174_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4274 G)) : AssociativeTheory144 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4271 := Equation4274_4512_implies_Equation4271 G h4274 h4512
  have h4272 := Equation4274_4512_implies_Equation4272 G h4274 h4512
  exact ⟨h4271, h4272, h4512⟩

private theorem AT174_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4275 G)) : AssociativeTheory154 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  exact ⟨h4272, h4275, h4512⟩

private theorem AT174_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4276 G)) : AssociativeTheory180 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4276, h4284, h4512⟩

private theorem AT174_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4277 G)) : AssociativeTheory139 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4277_4512_implies_Equation4268 G h4277 h4512
  have h4275 := Equation4277_4512_implies_Equation4275 G h4277 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  exact ⟨h4268, h4272, h4512⟩

private theorem AT174_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4278 G)) : AssociativeTheory160 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4278, h4512⟩

private theorem AT174_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4279 G)) : AssociativeTheory179 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4273 := Equation4279_4512_implies_Equation4273 G h4279 h4512
  exact ⟨h4273, h4284, h4512⟩

private theorem AT174_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4280 G)) : AssociativeTheory139 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4270 := Equation4280_4512_implies_Equation4270 G h4280 h4512
  have h4272 := Equation4280_4512_implies_Equation4272 G h4280 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  exact ⟨h4268, h4272, h4512⟩

private theorem AT174_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4283 G)) : AssociativeTheory182 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4283, h4284, h4512⟩

private theorem AT174_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4284 G)) : AssociativeTheory174 G := by
  obtain ⟨hh, h4284⟩ := h
  exact hh

private theorem AT174_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4286 G)) : AssociativeTheory135 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h4270 := Equation4268_4284_4512_implies_Equation4270 G h4268 h4284 h4512
  exact ⟨h4268, h4269, h4270, h4512⟩

private theorem AT174_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4287 G)) : AssociativeTheory185 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4287, h4512⟩

private theorem AT174_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4288 G)) : AssociativeTheory133 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4270 := Equation4288_4512_implies_Equation4270 G h4288 h4512
  exact ⟨h4268, h4270, h4512⟩

private theorem AT174_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4290 G)) : AssociativeTheory198 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4290, h4512⟩

private theorem AT174_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4291 G)) : AssociativeTheory217 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4291, h4512⟩

private theorem AT174_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4293 G)) : AssociativeTheory198 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4290 := Equation4284_4293_4512_implies_Equation4290 G h4284 h4293 h4512
  exact ⟨h4284, h4290, h4512⟩

private theorem AT174_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4296 G)) : AssociativeTheory155 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4269 := Equation4296_4512_implies_Equation4269 G h4296 h4512
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  exact ⟨h4269, h4272, h4275, h4512⟩

private theorem AT174_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4297 G)) : AssociativeTheory139 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4270 := Equation4297_4512_implies_Equation4270 G h4297 h4512
  have h4275 := Equation4297_4512_implies_Equation4275 G h4297 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  exact ⟨h4268, h4272, h4512⟩

private theorem AT174_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4299 G)) : AssociativeTheory139 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4299_4512_implies_Equation4268 G h4299 h4512
  have h4272 := Equation4299_4512_implies_Equation4272 G h4299 h4512
  exact ⟨h4268, h4272, h4512⟩

private theorem AT174_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4300 G)) : AssociativeTheory160 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4272 := Equation4300_4512_implies_Equation4272 G h4300 h4512
  have h4291 := Equation4300_4512_implies_Equation4291 G h4300 h4512
  have h4320 := Equation4284_4291_4512_implies_Equation4320 G h4284 h4291 h4512
  have h4269 := Equation4272_4320_4512_implies_Equation4269 G h4272 h4320 h4512
  have h4278 := Equation4269_4300_4512_implies_Equation4278 G h4269 h4300 h4512
  exact ⟨h4278, h4512⟩

private theorem AT174_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4301 G)) : AssociativeTheory141 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4301_4512_implies_Equation4268 G h4301 h4512
  have h4269 := Equation4301_4512_implies_Equation4269 G h4301 h4512
  have h4275 := Equation4301_4512_implies_Equation4275 G h4301 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  exact ⟨h4268, h4269, h4272, h4512⟩

private theorem AT174_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4304 G)) : AssociativeTheory154 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h4275 := Equation4304_4512_implies_Equation4275 G h4304 h4512
  exact ⟨h4272, h4275, h4512⟩

private theorem AT174_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4305 G)) : AssociativeTheory141 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h4275 := Equation4305_4512_implies_Equation4275 G h4305 h4512
  have h4283 := Equation4305_4512_implies_Equation4283 G h4305 h4512
  have h4269 := Equation4273_4284_4512_implies_Equation4269 G h4273 h4284 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  exact ⟨h4268, h4269, h4272, h4512⟩

private theorem AT174_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4314 G)) : AssociativeTheory182 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4283 := Equation4284_4314_4512_implies_Equation4283 G h4284 h4314 h4512
  exact ⟨h4283, h4284, h4512⟩

private theorem AT174_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4315 G)) : AssociativeTheory136 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4268 := Equation4315_4512_implies_Equation4268 G h4315 h4512
  have h4314 := Equation4315_4512_implies_Equation4314 G h4315 h4512
  have h4283 := Equation4284_4314_4512_implies_Equation4283 G h4284 h4314 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h4271 := Equation4269_4315_4512_implies_Equation4271 G h4269 h4315 h4512
  exact ⟨h4271, h4512⟩

private theorem AT174_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4318 G)) : AssociativeTheory135 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4270 := Equation4318_4512_implies_Equation4270 G h4318 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  exact ⟨h4268, h4269, h4270, h4512⟩

private theorem AT174_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4320 G)) : AssociativeTheory217 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4291 := Equation4284_4320_4512_implies_Equation4291 G h4284 h4320 h4512
  exact ⟨h4284, h4291, h4512⟩

private theorem AT174_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4321 G)) : AssociativeTheory274 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4321, h4512⟩

private theorem AT174_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4325 G)) : AssociativeTheory141 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4270 := Equation4325_4512_implies_Equation4270 G h4325 h4512
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h4320 := Equation4325_4512_implies_Equation4320 G h4325 h4512
  have h4269 := Equation4273_4284_4512_implies_Equation4269 G h4273 h4284 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  have h4272 := Equation4269_4320_4512_implies_Equation4272 G h4269 h4320 h4512
  exact ⟨h4268, h4269, h4272, h4512⟩

private theorem AT174_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4327 G)) : AssociativeTheory155 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4272 := Equation4327_4512_implies_Equation4272 G h4327 h4512
  have h4275 := Equation4272_4284_4512_implies_Equation4275 G h4272 h4284 h4512
  exact ⟨h4269, h4272, h4275, h4512⟩

private theorem AT174_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4331 G)) : AssociativeTheory141 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4269 := Equation4331_4512_implies_Equation4269 G h4331 h4512
  have h4270 := Equation4331_4512_implies_Equation4270 G h4331 h4512
  have h4272 := Equation4331_4512_implies_Equation4272 G h4331 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  exact ⟨h4268, h4269, h4272, h4512⟩

private theorem AT174_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4343 G)) : AssociativeTheory198 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  have h4290 := Equation4284_4343_4512_implies_Equation4290 G h4284 h4343 h4512
  exact ⟨h4284, h4290, h4512⟩

private theorem AT174_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4358 G)) : AssociativeTheory332 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4358, h4512⟩

private theorem AT174_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4362 G)) : AssociativeTheory381 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4362, h4512⟩

private theorem AT174_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4364 G)) : AssociativeTheory417 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4364, h4512⟩

private theorem AT174_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4369 G)) : AssociativeTheory440 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at174
  obtain ⟨h1, h4284, h4512⟩ := g hh
  exact ⟨h4284, h4369, h4512⟩

private theorem AT174_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory174 G) ∧ (Equation4512 G)) : AssociativeTheory174 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT174_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj174 eqid)) : (AssociativeTheory174 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj174 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at174 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT174_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory174 G) ∧ (EQeq G eqid) <-> (ATearly G (conj174 eqid)) :=
⟨match eqid with
| eq1 => AT174_Equation1_implies G
| eq2 => AT174_Equation2_implies G
| eq3 => AT174_Equation3_implies G
| eq4 => AT174_Equation4_implies G
| eq5 => AT174_Equation5_implies G
| eq8 => AT174_Equation8_implies G
| eq10 => AT174_Equation10_implies G
| eq11 => AT174_Equation11_implies G
| eq14 => AT174_Equation14_implies G
| eq16 => AT174_Equation16_implies G
| eq38 => AT174_Equation38_implies G
| eq39 => AT174_Equation39_implies G
| eq40 => AT174_Equation40_implies G
| eq41 => AT174_Equation41_implies G
| eq43 => AT174_Equation43_implies G
| eq47 => AT174_Equation47_implies G
| eq56 => AT174_Equation56_implies G
| eq66 => AT174_Equation66_implies G
| eq75 => AT174_Equation75_implies G
| eq307 => AT174_Equation307_implies G
| eq308 => AT174_Equation308_implies G
| eq309 => AT174_Equation309_implies G
| eq310 => AT174_Equation310_implies G
| eq311 => AT174_Equation311_implies G
| eq312 => AT174_Equation312_implies G
| eq313 => AT174_Equation313_implies G
| eq314 => AT174_Equation314_implies G
| eq315 => AT174_Equation315_implies G
| eq316 => AT174_Equation316_implies G
| eq318 => AT174_Equation318_implies G
| eq323 => AT174_Equation323_implies G
| eq325 => AT174_Equation325_implies G
| eq326 => AT174_Equation326_implies G
| eq327 => AT174_Equation327_implies G
| eq329 => AT174_Equation329_implies G
| eq332 => AT174_Equation332_implies G
| eq333 => AT174_Equation333_implies G
| eq343 => AT174_Equation343_implies G
| eq411 => AT174_Equation411_implies G
| eq419 => AT174_Equation419_implies G
| eq429 => AT174_Equation429_implies G
| eq440 => AT174_Equation440_implies G
| eq477 => AT174_Equation477_implies G
| eq504 => AT174_Equation504_implies G
| eq513 => AT174_Equation513_implies G
| eq3253 => AT174_Equation3253_implies G
| eq3255 => AT174_Equation3255_implies G
| eq3256 => AT174_Equation3256_implies G
| eq3258 => AT174_Equation3258_implies G
| eq3259 => AT174_Equation3259_implies G
| eq3260 => AT174_Equation3260_implies G
| eq3261 => AT174_Equation3261_implies G
| eq3264 => AT174_Equation3264_implies G
| eq3265 => AT174_Equation3265_implies G
| eq3267 => AT174_Equation3267_implies G
| eq3271 => AT174_Equation3271_implies G
| eq3273 => AT174_Equation3273_implies G
| eq3274 => AT174_Equation3274_implies G
| eq3275 => AT174_Equation3275_implies G
| eq3277 => AT174_Equation3277_implies G
| eq3278 => AT174_Equation3278_implies G
| eq3290 => AT174_Equation3290_implies G
| eq3292 => AT174_Equation3292_implies G
| eq3300 => AT174_Equation3300_implies G
| eq3306 => AT174_Equation3306_implies G
| eq3308 => AT174_Equation3308_implies G
| eq3309 => AT174_Equation3309_implies G
| eq3315 => AT174_Equation3315_implies G
| eq3316 => AT174_Equation3316_implies G
| eq3319 => AT174_Equation3319_implies G
| eq3322 => AT174_Equation3322_implies G
| eq3323 => AT174_Equation3323_implies G
| eq3326 => AT174_Equation3326_implies G
| eq3331 => AT174_Equation3331_implies G
| eq3334 => AT174_Equation3334_implies G
| eq3342 => AT174_Equation3342_implies G
| eq3346 => AT174_Equation3346_implies G
| eq3350 => AT174_Equation3350_implies G
| eq3353 => AT174_Equation3353_implies G
| eq3388 => AT174_Equation3388_implies G
| eq3414 => AT174_Equation3414_implies G
| eq4268 => AT174_Equation4268_implies G
| eq4269 => AT174_Equation4269_implies G
| eq4270 => AT174_Equation4270_implies G
| eq4271 => AT174_Equation4271_implies G
| eq4272 => AT174_Equation4272_implies G
| eq4273 => AT174_Equation4273_implies G
| eq4274 => AT174_Equation4274_implies G
| eq4275 => AT174_Equation4275_implies G
| eq4276 => AT174_Equation4276_implies G
| eq4277 => AT174_Equation4277_implies G
| eq4278 => AT174_Equation4278_implies G
| eq4279 => AT174_Equation4279_implies G
| eq4280 => AT174_Equation4280_implies G
| eq4283 => AT174_Equation4283_implies G
| eq4284 => AT174_Equation4284_implies G
| eq4286 => AT174_Equation4286_implies G
| eq4287 => AT174_Equation4287_implies G
| eq4288 => AT174_Equation4288_implies G
| eq4290 => AT174_Equation4290_implies G
| eq4291 => AT174_Equation4291_implies G
| eq4293 => AT174_Equation4293_implies G
| eq4296 => AT174_Equation4296_implies G
| eq4297 => AT174_Equation4297_implies G
| eq4299 => AT174_Equation4299_implies G
| eq4300 => AT174_Equation4300_implies G
| eq4301 => AT174_Equation4301_implies G
| eq4304 => AT174_Equation4304_implies G
| eq4305 => AT174_Equation4305_implies G
| eq4314 => AT174_Equation4314_implies G
| eq4315 => AT174_Equation4315_implies G
| eq4318 => AT174_Equation4318_implies G
| eq4320 => AT174_Equation4320_implies G
| eq4321 => AT174_Equation4321_implies G
| eq4325 => AT174_Equation4325_implies G
| eq4327 => AT174_Equation4327_implies G
| eq4331 => AT174_Equation4331_implies G
| eq4343 => AT174_Equation4343_implies G
| eq4358 => AT174_Equation4358_implies G
| eq4362 => AT174_Equation4362_implies G
| eq4364 => AT174_Equation4364_implies G
| eq4369 => AT174_Equation4369_implies G
| eq4512 => AT174_Equation4512_implies G
, AT174_conj_implied G eqid⟩

