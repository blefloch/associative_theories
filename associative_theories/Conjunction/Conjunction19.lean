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


def conj19 : EQIndex → ATIndex
| eq1 => at19
| eq2 => at2
| eq3 => at3
| eq4 => at4
| eq5 => at5
| eq8 => at3
| eq10 => at7
| eq11 => at4
| eq14 => at2
| eq16 => at5
| eq38 => at4
| eq39 => at5
| eq40 => at2
| eq41 => at2
| eq43 => at20
| eq47 => at19
| eq56 => at21
| eq66 => at22
| eq75 => at23
| eq307 => at3
| eq308 => at4
| eq309 => at7
| eq310 => at4
| eq311 => at4
| eq312 => at5
| eq313 => at2
| eq314 => at2
| eq315 => at5
| eq316 => at2
| eq318 => at5
| eq323 => at3
| eq325 => at46
| eq326 => at3
| eq327 => at4
| eq329 => at7
| eq332 => at16
| eq333 => at52
| eq343 => at5
| eq411 => at3
| eq419 => at7
| eq429 => at7
| eq440 => at4
| eq477 => at2
| eq504 => at2
| eq513 => at5
| eq3253 => at3
| eq3255 => at7
| eq3256 => at4
| eq3258 => at7
| eq3259 => at4
| eq3260 => at4
| eq3261 => at7
| eq3264 => at7
| eq3265 => at4
| eq3267 => at4
| eq3271 => at5
| eq3273 => at2
| eq3274 => at5
| eq3275 => at2
| eq3277 => at2
| eq3278 => at5
| eq3290 => at2
| eq3292 => at5
| eq3300 => at5
| eq3306 => at3
| eq3308 => at46
| eq3309 => at3
| eq3315 => at46
| eq3316 => at3
| eq3319 => at3
| eq3322 => at7
| eq3323 => at4
| eq3326 => at7
| eq3331 => at4
| eq3334 => at7
| eq3342 => at16
| eq3346 => at52
| eq3350 => at2
| eq3353 => at52
| eq3388 => at5
| eq3414 => at5
| eq4268 => at4
| eq4269 => at7
| eq4270 => at4
| eq4271 => at4
| eq4272 => at5
| eq4273 => at2
| eq4274 => at2
| eq4275 => at5
| eq4276 => at24
| eq4277 => at2
| eq4278 => at5
| eq4279 => at2
| eq4280 => at2
| eq4283 => at162
| eq4284 => at3
| eq4286 => at4
| eq4287 => at7
| eq4288 => at4
| eq4290 => at20
| eq4291 => at52
| eq4293 => at16
| eq4296 => at5
| eq4297 => at2
| eq4299 => at2
| eq4300 => at5
| eq4301 => at2
| eq4304 => at5
| eq4305 => at2
| eq4314 => at46
| eq4315 => at4
| eq4318 => at4
| eq4320 => at242
| eq4321 => at16
| eq4325 => at2
| eq4327 => at5
| eq4331 => at2
| eq4343 => at16
| eq4358 => at310
| eq4362 => at355
| eq4364 => at20
| eq4369 => at20
| eq4512 => at19


private theorem AT19_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation1 G)) : AssociativeTheory19 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT19_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT19_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h3, h4512⟩

private theorem AT19_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h4, h4512⟩

private theorem AT19_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation5 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h5, h4512⟩

private theorem AT19_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation8 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation8_4512_implies_Equation3253 G h8 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation10 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h10, h4512⟩

private theorem AT19_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation11 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h411 := Equation11_4512_implies_Equation411 G h11 h4512
  have h429 := Equation11_4512_implies_Equation429 G h11 h4512
  have h3315 := Equation11_4512_implies_Equation3315 G h11 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation14_4512_implies_Equation4273 G h14 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation16 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h411 := Equation16_4512_implies_Equation411 G h16 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation38 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h325 := Equation38_4512_implies_Equation325 G h38 h4512
  have h3261 := Equation38_4512_implies_Equation3261 G h38 h4512
  have h4268 := Equation38_4512_implies_Equation4268 G h38 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation39 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h333 := Equation39_4512_implies_Equation333 G h39 h4512
  have h3261 := Equation39_4512_implies_Equation3261 G h39 h4512
  have h4269 := Equation39_4512_implies_Equation4269 G h39 h4512
  have h3 := Equation47_4269_4512_implies_Equation3 G h47 h4269 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation40 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4270 := Equation40_4512_implies_Equation4270 G h40 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation41 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation41_4512_implies_Equation4273 G h41 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation43 G)) : AssociativeTheory20 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h43, h47, h4512⟩

private theorem AT19_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation47 G)) : AssociativeTheory19 G := by
  obtain ⟨hh, h47⟩ := h
  exact hh

private theorem AT19_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation56 G)) : AssociativeTheory21 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h56, h4512⟩

private theorem AT19_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation66 G)) : AssociativeTheory22 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h43 := Equation66_4512_implies_Equation43 G h66 h4512
  have h56 := Equation66_4512_implies_Equation56 G h66 h4512
  exact ⟨h43, h56, h4512⟩

private theorem AT19_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation75 G)) : AssociativeTheory23 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h75, h4512⟩

private theorem AT19_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation307 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h307⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation307_4512_implies_Equation3253 G h307 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation308 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h307 := Equation308_4512_implies_Equation307 G h308 h4512
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation309 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h3 := Equation47_4269_4512_implies_Equation3 G h47 h4269 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation310 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h307 := Equation310_4512_implies_Equation307 G h310 h4512
  have h3256 := Equation310_4512_implies_Equation3256 G h310 h4512
  have h3261 := Equation310_4512_implies_Equation3261 G h310 h4512
  have h4268 := Equation310_4512_implies_Equation4268 G h310 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation311 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation311_4512_implies_Equation3261 G h311 h4512
  have h4314 := Equation311_4512_implies_Equation4314 G h311 h4512
  have h3 := Equation47_4314_4512_implies_Equation3 G h47 h4314 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation312 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h4272 := Equation312_4512_implies_Equation4272 G h312 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h343 := Equation312_323_4512_implies_Equation343 G h312 h323 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h333 := Equation343_4512_implies_Equation333 G h343 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation313 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation313_4512_implies_Equation4273 G h313 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation314 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation314_4512_implies_Equation4273 G h314 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation315 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation315_4512_implies_Equation3261 G h315 h4512
  have h4272 := Equation315_4512_implies_Equation4272 G h315 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h333 := Equation39_4512_implies_Equation333 G h39 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation316 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4275 := Equation316_4512_implies_Equation4275 G h316 h4512
  have h4276 := Equation316_4512_implies_Equation4276 G h316 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation318 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation318_4512_implies_Equation3261 G h318 h4512
  have h4291 := Equation318_4512_implies_Equation4291 G h318 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation323 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation323_4512_implies_Equation3253 G h323 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation325 G)) : AssociativeTheory46 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation325_4512_implies_Equation3253 G h325 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h325, h4512⟩

private theorem AT19_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation326 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation326_4512_implies_Equation3253 G h326 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation327 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  have h3255 := Equation327_4512_implies_Equation3255 G h327 h4512
  have h4314 := Equation327_4512_implies_Equation4314 G h327 h4512
  have h3 := Equation47_4314_4512_implies_Equation3 G h47 h4314 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation329 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation329_4512_implies_Equation3261 G h329 h4512
  have h4269 := Equation329_4512_implies_Equation4269 G h329 h4512
  have h3 := Equation47_4269_4512_implies_Equation3 G h47 h4269 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation332 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h43 := Equation332_4512_implies_Equation43 G h332 h4512
  have h3253 := Equation332_4512_implies_Equation3253 G h332 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT19_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation333 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4291 := Equation333_4512_implies_Equation4291 G h333 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT19_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation343 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h333 := Equation343_4512_implies_Equation333 G h343 h4512
  have h3278 := Equation343_4512_implies_Equation3278 G h343 h4512
  have h4291 := Equation343_4512_implies_Equation4291 G h343 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation411 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation419 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3253 := Equation419_4512_implies_Equation3253 G h419 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation429 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation429_4512_implies_Equation3253 G h429 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation440 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h429 := Equation11_4512_implies_Equation429 G h11 h4512
  have h3315 := Equation11_4512_implies_Equation3315 G h11 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  have h4320 := Equation477_4512_implies_Equation4320 G h477 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h4290 := Equation504_4512_implies_Equation4290 G h504 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation513 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h3 := Equation47_411_4512_implies_Equation3 G h47 h411 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3253 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3253⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3255 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3255_4512_implies_Equation3253 G h3255 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3256 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3256_4512_implies_Equation3253 G h3256 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3306 := Equation3_4512_implies_Equation3306 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3258 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3258_4512_implies_Equation3253 G h3258 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h3255 := Equation3258_4284_4512_implies_Equation3255 G h3258 h4284 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3259 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h4270 := Equation3259_4512_implies_Equation4270 G h3259 h4512
  have h3 := Equation47_4270_4512_implies_Equation3 G h47 h4270 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3260 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h307 := Equation3260_4512_implies_Equation307 G h3260 h4512
  have h3256 := Equation3260_4512_implies_Equation3256 G h3260 h4512
  have h3261 := Equation3260_4512_implies_Equation3261 G h3260 h4512
  have h4268 := Equation3260_4512_implies_Equation4268 G h3260 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3261 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3261_4512_implies_Equation3253 G h3261 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3264 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3264_4512_implies_Equation3253 G h3264 h4512
  have h3261 := Equation3264_4512_implies_Equation3261 G h3264 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3265 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h307 := Equation3265_4512_implies_Equation307 G h3265 h4512
  have h3256 := Equation3265_4512_implies_Equation3256 G h3265 h4512
  have h3261 := Equation3265_4512_implies_Equation3261 G h3265 h4512
  have h4268 := Equation3265_4512_implies_Equation4268 G h3265 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3267 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h307 := Equation3267_4512_implies_Equation307 G h3267 h4512
  have h3256 := Equation3267_4512_implies_Equation3256 G h3267 h4512
  have h3261 := Equation3267_4512_implies_Equation3261 G h3267 h4512
  have h4268 := Equation3267_4512_implies_Equation4268 G h3267 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3271 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h4275 := Equation3271_4512_implies_Equation4275 G h3271 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3306 := Equation3_4512_implies_Equation3306 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3414 := Equation3278_3306_4512_implies_Equation3414 G h3278 h3306 h4512
  have h3353 := Equation3414_4512_implies_Equation3353 G h3414 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4275 := Equation3273_4512_implies_Equation4275 G h3273 h4512
  have h4276 := Equation3273_4512_implies_Equation4276 G h3273 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3274 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h315 := Equation3274_4512_implies_Equation315 G h3274 h4512
  have h3261 := Equation3274_4512_implies_Equation3261 G h3274 h4512
  have h4272 := Equation3274_4512_implies_Equation4272 G h3274 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h333 := Equation39_4512_implies_Equation333 G h39 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3275 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4275 := Equation3275_4512_implies_Equation4275 G h3275 h4512
  have h4276 := Equation3275_4512_implies_Equation4276 G h3275 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4275 := Equation3277_4512_implies_Equation4275 G h3277 h4512
  have h4276 := Equation3277_4512_implies_Equation4276 G h3277 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3278 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3278_4512_implies_Equation3253 G h3278 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3306 := Equation3_4512_implies_Equation3306 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3414 := Equation3278_3306_4512_implies_Equation3414 G h3278 h3306 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3353 := Equation3414_4512_implies_Equation3353 G h3414 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3290 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4275 := Equation3290_4512_implies_Equation4275 G h3290 h4512
  have h4276 := Equation3290_4512_implies_Equation4276 G h3290 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3292 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h315 := Equation3292_4512_implies_Equation315 G h3292 h4512
  have h3261 := Equation3292_4512_implies_Equation3261 G h3292 h4512
  have h4272 := Equation3292_4512_implies_Equation4272 G h3292 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h333 := Equation39_4512_implies_Equation333 G h39 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3300 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h315 := Equation3300_4512_implies_Equation315 G h3300 h4512
  have h3261 := Equation3300_4512_implies_Equation3261 G h3300 h4512
  have h4272 := Equation3300_4512_implies_Equation4272 G h3300 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h333 := Equation39_4512_implies_Equation333 G h39 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3306 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3306_4512_implies_Equation3253 G h3306 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3308 G)) : AssociativeTheory46 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3308_4512_implies_Equation3253 G h3308 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h3, h325, h4512⟩

private theorem AT19_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3309 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3309_4512_implies_Equation3253 G h3309 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3315 G)) : AssociativeTheory46 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3315_4512_implies_Equation3253 G h3315 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h3, h325, h4512⟩

private theorem AT19_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3316 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3316_4512_implies_Equation3253 G h3316 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3319 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3319_4512_implies_Equation3253 G h3319 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3322 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3322_4512_implies_Equation3253 G h3322 h4512
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3323 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3323_4512_implies_Equation3253 G h3323 h4512
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3306 := Equation3_4512_implies_Equation3306 G h3 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3326 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3326_4512_implies_Equation3253 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h3255 := Equation3258_4284_4512_implies_Equation3255 G h3258 h4284 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3331 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h4270 := Equation3331_4512_implies_Equation4270 G h3331 h4512
  have h3 := Equation47_4270_4512_implies_Equation3 G h47 h4270 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3334 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3334_4512_implies_Equation3253 G h3334 h4512
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3342 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h43 := Equation3342_4512_implies_Equation43 G h3342 h4512
  have h3253 := Equation3342_4512_implies_Equation3253 G h3342 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT19_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3346 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3346_4512_implies_Equation3253 G h3346 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT19_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3350 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation3350_4512_implies_Equation4273 G h3350 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3353 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3353_4512_implies_Equation3253 G h3353 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT19_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3388 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3261 := Equation3388_4512_implies_Equation3261 G h3388 h4512
  have h3353 := Equation3388_4512_implies_Equation3353 G h3388 h4512
  have h4275 := Equation3388_4512_implies_Equation4275 G h3388 h4512
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation3414 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3253 := Equation3414_4512_implies_Equation3253 G h3414 h4512
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h3353 := Equation3414_4512_implies_Equation3353 G h3414 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4268 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h310 := Equation308_4284_4512_implies_Equation310 G h308 h4284 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h3261 := Equation310_4512_implies_Equation3261 G h310 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4269 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4269_4512_implies_Equation3 G h47 h4269 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4270 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4270_4512_implies_Equation3 G h47 h4270 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4271 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4269 := Equation4271_4512_implies_Equation4269 G h4271 h4512
  have h4314 := Equation4271_4512_implies_Equation4314 G h4271 h4512
  have h3 := Equation47_4314_4512_implies_Equation3 G h47 h4314 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4272 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h343 := Equation312_323_4512_implies_Equation343 G h312 h323 h4512
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h333 := Equation343_4512_implies_Equation333 G h343 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4274 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation4274_4512_implies_Equation4273 G h4274 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4275 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4275_4512_implies_Equation3 G h47 h4275 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4272 := Equation4275_4284_4512_implies_Equation4272 G h4275 h4284 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h343 := Equation312_323_4512_implies_Equation343 G h312 h323 h4512
  have h333 := Equation343_4512_implies_Equation333 G h343 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4276 G)) : AssociativeTheory24 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h56 := Equation47_4276_4512_implies_Equation56 G h47 h4276 h4512
  have h75 := Equation47_4276_4512_implies_Equation75 G h47 h4276 h4512
  exact ⟨h56, h75, h4512⟩

private theorem AT19_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h4293 := Equation4277_4512_implies_Equation4293 G h4277 h4512
  have h3 := Equation47_4293_4512_implies_Equation3 G h47 h4293 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4278 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4269 := Equation4278_4512_implies_Equation4269 G h4278 h4512
  have h4291 := Equation4278_4512_implies_Equation4291 G h4278 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
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

private theorem AT19_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4279 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation4279_4512_implies_Equation4273 G h4279 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4280 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4270 := Equation4280_4512_implies_Equation4270 G h4280 h4512
  have h4276 := Equation4280_4512_implies_Equation4276 G h4280 h4512
  have h3 := Equation47_4270_4512_implies_Equation3 G h47 h4270 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4283 G)) : AssociativeTheory162 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h47, h4283, h4512⟩

private theorem AT19_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4284 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  exact ⟨h3, h4512⟩

private theorem AT19_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4286 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h4283 := Equation4286_4512_implies_Equation4283 G h4286 h4512
  have h3 := Equation47_4268_4512_implies_Equation3 G h47 h4268 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4287 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4269 := Equation4287_4512_implies_Equation4269 G h4287 h4512
  have h4284 := Equation4287_4512_implies_Equation4284 G h4287 h4512
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT19_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4288 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4270 := Equation4288_4512_implies_Equation4270 G h4288 h4512
  have h4284 := Equation4288_4512_implies_Equation4284 G h4288 h4512
  have h3 := Equation47_4284_4512_implies_Equation3 G h47 h4284 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4290 G)) : AssociativeTheory20 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  exact ⟨h43, h47, h4512⟩

private theorem AT19_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4291 G)) : AssociativeTheory52 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h3, h333, h4512⟩

private theorem AT19_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4293 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4293_4512_implies_Equation3 G h47 h4293 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT19_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4296 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  have h4291 := Equation4296_4512_implies_Equation4291 G h4296 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
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

private theorem AT19_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4297 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4270 := Equation4297_4512_implies_Equation4270 G h4297 h4512
  have h4290 := Equation4297_4512_implies_Equation4290 G h4297 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4299 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4276 := Equation4299_4512_implies_Equation4276 G h4299 h4512
  have h4293 := Equation4299_4512_implies_Equation4293 G h4299 h4512
  have h3 := Equation47_4293_4512_implies_Equation3 G h47 h4293 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4300 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4272 := Equation4300_4512_implies_Equation4272 G h4300 h4512
  have h4291 := Equation4300_4512_implies_Equation4291 G h4300 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h4320 := Equation4284_4291_4512_implies_Equation4320 G h4284 h4291 h4512
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h3261 := Equation3278_4320_4512_implies_Equation3261 G h3278 h4320 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4301 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation4301_4512_implies_Equation4273 G h4301 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4304 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h4275 := Equation4304_4512_implies_Equation4275 G h4304 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h343 := Equation312_323_4512_implies_Equation343 G h312 h323 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h333 := Equation343_4512_implies_Equation333 G h343 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT19_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4305 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4314 G)) : AssociativeTheory46 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4314_4512_implies_Equation3 G h47 h4314 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  exact ⟨h3, h325, h4512⟩

private theorem AT19_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4315 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4268 := Equation4315_4512_implies_Equation4268 G h4315 h4512
  have h4314 := Equation4315_4512_implies_Equation4314 G h4315 h4512
  have h3 := Equation47_4314_4512_implies_Equation3 G h47 h4314 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h3253 := Equation3_4512_implies_Equation3253 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h4270 := Equation4268_4284_4512_implies_Equation4270 G h4268 h4284 h4512
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4318 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4314 := Equation4318_4512_implies_Equation4314 G h4318 h4512
  have h3 := Equation47_4314_4512_implies_Equation3 G h47 h4314 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3261 := Equation309_4512_implies_Equation3261 G h309 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT19_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4320 G)) : AssociativeTheory242 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h47, h4320, h4512⟩

private theorem AT19_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4321 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4321_4512_implies_Equation3 G h47 h4321 h4512
  have h307 := Equation3_4512_implies_Equation307 G h3 h4512
  have h323 := Equation3_4512_implies_Equation323 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4293 := Equation307_4284_4321_4512_implies_Equation4293 G h307 h4284 h4321 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT19_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4325 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4327 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4272 := Equation4327_4512_implies_Equation4272 G h4327 h4512
  have h4320 := Equation4327_4512_implies_Equation4320 G h4327 h4512
  have h3 := Equation47_4272_4512_implies_Equation3 G h47 h4272 h4512
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

private theorem AT19_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4331 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4273 := Equation4331_4512_implies_Equation4273 G h4331 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT19_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4343 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h3 := Equation47_4343_4512_implies_Equation3 G h47 h4343 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h43 := Equation326_4343_4512_implies_Equation43 G h326 h4343 h4512
  exact ⟨h3, h43, h4512⟩

private theorem AT19_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4358 G)) : AssociativeTheory310 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h47, h4358, h4512⟩

private theorem AT19_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4362 G)) : AssociativeTheory355 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  exact ⟨h47, h4362, h4512⟩

private theorem AT19_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4364 G)) : AssociativeTheory20 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4290 := Equation4364_4512_implies_Equation4290 G h4364 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  exact ⟨h43, h47, h4512⟩

private theorem AT19_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4369 G)) : AssociativeTheory20 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at19
  obtain ⟨h1, h47, h4512⟩ := g hh
  have h4290 := Equation4369_4512_implies_Equation4290 G h4369 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  exact ⟨h43, h47, h4512⟩

private theorem AT19_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory19 G) ∧ (Equation4512 G)) : AssociativeTheory19 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT19_conj_implied (eqid : EQIndex) (G: Type*) [Magma G] (h : ATearly G (conj19 eqid)) : (AssociativeTheory19 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj19 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at19 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT19_conj (eqid : EQIndex) (G: Type*) [Magma G] : (AssociativeTheory19 G) ∧ (EQeq G eqid) <-> (ATearly G (conj19 eqid)) :=
⟨match eqid with
| eq1 => AT19_Equation1_implies G
| eq2 => AT19_Equation2_implies G
| eq3 => AT19_Equation3_implies G
| eq4 => AT19_Equation4_implies G
| eq5 => AT19_Equation5_implies G
| eq8 => AT19_Equation8_implies G
| eq10 => AT19_Equation10_implies G
| eq11 => AT19_Equation11_implies G
| eq14 => AT19_Equation14_implies G
| eq16 => AT19_Equation16_implies G
| eq38 => AT19_Equation38_implies G
| eq39 => AT19_Equation39_implies G
| eq40 => AT19_Equation40_implies G
| eq41 => AT19_Equation41_implies G
| eq43 => AT19_Equation43_implies G
| eq47 => AT19_Equation47_implies G
| eq56 => AT19_Equation56_implies G
| eq66 => AT19_Equation66_implies G
| eq75 => AT19_Equation75_implies G
| eq307 => AT19_Equation307_implies G
| eq308 => AT19_Equation308_implies G
| eq309 => AT19_Equation309_implies G
| eq310 => AT19_Equation310_implies G
| eq311 => AT19_Equation311_implies G
| eq312 => AT19_Equation312_implies G
| eq313 => AT19_Equation313_implies G
| eq314 => AT19_Equation314_implies G
| eq315 => AT19_Equation315_implies G
| eq316 => AT19_Equation316_implies G
| eq318 => AT19_Equation318_implies G
| eq323 => AT19_Equation323_implies G
| eq325 => AT19_Equation325_implies G
| eq326 => AT19_Equation326_implies G
| eq327 => AT19_Equation327_implies G
| eq329 => AT19_Equation329_implies G
| eq332 => AT19_Equation332_implies G
| eq333 => AT19_Equation333_implies G
| eq343 => AT19_Equation343_implies G
| eq411 => AT19_Equation411_implies G
| eq419 => AT19_Equation419_implies G
| eq429 => AT19_Equation429_implies G
| eq440 => AT19_Equation440_implies G
| eq477 => AT19_Equation477_implies G
| eq504 => AT19_Equation504_implies G
| eq513 => AT19_Equation513_implies G
| eq3253 => AT19_Equation3253_implies G
| eq3255 => AT19_Equation3255_implies G
| eq3256 => AT19_Equation3256_implies G
| eq3258 => AT19_Equation3258_implies G
| eq3259 => AT19_Equation3259_implies G
| eq3260 => AT19_Equation3260_implies G
| eq3261 => AT19_Equation3261_implies G
| eq3264 => AT19_Equation3264_implies G
| eq3265 => AT19_Equation3265_implies G
| eq3267 => AT19_Equation3267_implies G
| eq3271 => AT19_Equation3271_implies G
| eq3273 => AT19_Equation3273_implies G
| eq3274 => AT19_Equation3274_implies G
| eq3275 => AT19_Equation3275_implies G
| eq3277 => AT19_Equation3277_implies G
| eq3278 => AT19_Equation3278_implies G
| eq3290 => AT19_Equation3290_implies G
| eq3292 => AT19_Equation3292_implies G
| eq3300 => AT19_Equation3300_implies G
| eq3306 => AT19_Equation3306_implies G
| eq3308 => AT19_Equation3308_implies G
| eq3309 => AT19_Equation3309_implies G
| eq3315 => AT19_Equation3315_implies G
| eq3316 => AT19_Equation3316_implies G
| eq3319 => AT19_Equation3319_implies G
| eq3322 => AT19_Equation3322_implies G
| eq3323 => AT19_Equation3323_implies G
| eq3326 => AT19_Equation3326_implies G
| eq3331 => AT19_Equation3331_implies G
| eq3334 => AT19_Equation3334_implies G
| eq3342 => AT19_Equation3342_implies G
| eq3346 => AT19_Equation3346_implies G
| eq3350 => AT19_Equation3350_implies G
| eq3353 => AT19_Equation3353_implies G
| eq3388 => AT19_Equation3388_implies G
| eq3414 => AT19_Equation3414_implies G
| eq4268 => AT19_Equation4268_implies G
| eq4269 => AT19_Equation4269_implies G
| eq4270 => AT19_Equation4270_implies G
| eq4271 => AT19_Equation4271_implies G
| eq4272 => AT19_Equation4272_implies G
| eq4273 => AT19_Equation4273_implies G
| eq4274 => AT19_Equation4274_implies G
| eq4275 => AT19_Equation4275_implies G
| eq4276 => AT19_Equation4276_implies G
| eq4277 => AT19_Equation4277_implies G
| eq4278 => AT19_Equation4278_implies G
| eq4279 => AT19_Equation4279_implies G
| eq4280 => AT19_Equation4280_implies G
| eq4283 => AT19_Equation4283_implies G
| eq4284 => AT19_Equation4284_implies G
| eq4286 => AT19_Equation4286_implies G
| eq4287 => AT19_Equation4287_implies G
| eq4288 => AT19_Equation4288_implies G
| eq4290 => AT19_Equation4290_implies G
| eq4291 => AT19_Equation4291_implies G
| eq4293 => AT19_Equation4293_implies G
| eq4296 => AT19_Equation4296_implies G
| eq4297 => AT19_Equation4297_implies G
| eq4299 => AT19_Equation4299_implies G
| eq4300 => AT19_Equation4300_implies G
| eq4301 => AT19_Equation4301_implies G
| eq4304 => AT19_Equation4304_implies G
| eq4305 => AT19_Equation4305_implies G
| eq4314 => AT19_Equation4314_implies G
| eq4315 => AT19_Equation4315_implies G
| eq4318 => AT19_Equation4318_implies G
| eq4320 => AT19_Equation4320_implies G
| eq4321 => AT19_Equation4321_implies G
| eq4325 => AT19_Equation4325_implies G
| eq4327 => AT19_Equation4327_implies G
| eq4331 => AT19_Equation4331_implies G
| eq4343 => AT19_Equation4343_implies G
| eq4358 => AT19_Equation4358_implies G
| eq4362 => AT19_Equation4362_implies G
| eq4364 => AT19_Equation4364_implies G
| eq4369 => AT19_Equation4369_implies G
| eq4512 => AT19_Equation4512_implies G
, AT19_conj_implied eqid G⟩

