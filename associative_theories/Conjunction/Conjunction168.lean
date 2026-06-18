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


def conj168 : EQIndex → ATIndex
| eq1 => at168
| eq2 => at2
| eq3 => at46
| eq4 => at4
| eq5 => at2
| eq8 => at112
| eq10 => at4
| eq11 => at8
| eq14 => at9
| eq16 => at9
| eq38 => at11
| eq39 => at13
| eq40 => at146
| eq41 => at13
| eq43 => at64
| eq47 => at46
| eq56 => at4
| eq66 => at2
| eq75 => at2
| eq307 => at164
| eq308 => at32
| eq309 => at32
| eq310 => at32
| eq311 => at34
| eq312 => at31
| eq313 => at31
| eq314 => at35
| eq315 => at31
| eq316 => at31
| eq318 => at35
| eq323 => at48
| eq325 => at48
| eq326 => at165
| eq327 => at11
| eq329 => at11
| eq332 => at42
| eq333 => at42
| eq343 => at13
| eq411 => at112
| eq419 => at8
| eq429 => at8
| eq440 => at8
| eq477 => at9
| eq504 => at9
| eq513 => at9
| eq3253 => at168
| eq3255 => at32
| eq3256 => at169
| eq3258 => at32
| eq3259 => at169
| eq3260 => at32
| eq3261 => at169
| eq3264 => at32
| eq3265 => at32
| eq3267 => at92
| eq3271 => at146
| eq3273 => at31
| eq3274 => at31
| eq3275 => at31
| eq3277 => at93
| eq3278 => at146
| eq3290 => at31
| eq3292 => at31
| eq3300 => at93
| eq3306 => at111
| eq3308 => at111
| eq3309 => at48
| eq3315 => at111
| eq3316 => at48
| eq3319 => at170
| eq3322 => at11
| eq3323 => at107
| eq3326 => at11
| eq3331 => at107
| eq3334 => at107
| eq3342 => at106
| eq3346 => at106
| eq3350 => at105
| eq3353 => at106
| eq3388 => at105
| eq3414 => at105
| eq4268 => at32
| eq4269 => at32
| eq4270 => at169
| eq4271 => at34
| eq4272 => at31
| eq4273 => at146
| eq4274 => at35
| eq4275 => at146
| eq4276 => at31
| eq4277 => at31
| eq4278 => at35
| eq4279 => at31
| eq4280 => at31
| eq4283 => at168
| eq4284 => at183
| eq4286 => at32
| eq4287 => at34
| eq4288 => at32
| eq4290 => at196
| eq4291 => at213
| eq4293 => at213
| eq4296 => at31
| eq4297 => at146
| eq4299 => at31
| eq4300 => at35
| eq4301 => at31
| eq4304 => at31
| eq4305 => at146
| eq4314 => at183
| eq4315 => at34
| eq4318 => at32
| eq4320 => at196
| eq4321 => at213
| eq4325 => at146
| eq4327 => at31
| eq4331 => at31
| eq4343 => at203
| eq4358 => at317
| eq4362 => at379
| eq4364 => at412
| eq4369 => at438
| eq4512 => at168


private theorem AT168_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation1 G)) : AssociativeTheory168 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT168_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT168_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3 G)) : AssociativeTheory46 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  exact ⟨h3, h325, h4512⟩

private theorem AT168_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h4, h4512⟩

private theorem AT168_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation5 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h47 := Equation5_4512_implies_Equation47 G h5 h4512
  have h4275 := Equation5_4512_implies_Equation4275 G h5 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT168_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation8 G)) : AssociativeTheory112 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  exact ⟨h8, h3308, h4512⟩

private theorem AT168_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation10 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h326 := Equation10_4512_implies_Equation326 G h10 h4512
  have h4284 := Equation10_4512_implies_Equation4284 G h10 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT168_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation11 G)) : AssociativeTheory8 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h11, h4512⟩

private theorem AT168_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation14 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h14, h4512⟩

private theorem AT168_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation16 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h8 := Equation16_4512_implies_Equation8 G h16 h4512
  have h513 := Equation16_4512_implies_Equation513 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h4320 := Equation16_4512_implies_Equation4320 G h16 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h440 := Equation513_4290_4512_implies_Equation440 G h513 h4290 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT168_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation38 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h38, h4512⟩

private theorem AT168_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation39 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h326 := Equation39_4512_implies_Equation326 G h39 h4512
  have h3258 := Equation39_4512_implies_Equation3258 G h39 h4512
  have h4284 := Equation39_4512_implies_Equation4284 G h39 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT168_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation40 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4275 := Equation40_4512_implies_Equation4275 G h40 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h38 := Equation41_4512_implies_Equation38 G h41 h4512
  have h39 := Equation41_4512_implies_Equation39 G h41 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT168_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation43 G)) : AssociativeTheory64 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h43, h3253, h4512⟩

private theorem AT168_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation47 G)) : AssociativeTheory46 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h326 := Equation3_4512_implies_Equation326 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  exact ⟨h3, h325, h4512⟩

private theorem AT168_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation56 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h47 := Equation56_4512_implies_Equation47 G h56 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h4 := Equation3_56_4512_implies_Equation4 G h3 h56 h4512
  exact ⟨h4, h4512⟩

private theorem AT168_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h47 := Equation66_4512_implies_Equation47 G h66 h4512
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT168_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation75 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h43 := Equation75_4283_4512_implies_Equation43 G h75 h4283 h4512
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h56 := Equation43_75_4512_implies_Equation56 G h43 h75 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h4276 := Equation56_75_4512_implies_Equation4276 G h56 h75 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT168_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation307 G)) : AssociativeTheory164 G := by
  obtain ⟨hh, h307⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h307, h4283, h4512⟩

private theorem AT168_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation308 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation308_4512_implies_Equation307 G h308 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation309 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3255 := Equation309_4512_implies_Equation3255 G h309 h4512
  have h308 := Equation3255_4283_4512_implies_Equation308 G h3255 h4283 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation310 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation310_4512_implies_Equation307 G h310 h4512
  have h308 := Equation310_4512_implies_Equation308 G h310 h4512
  have h4268 := Equation310_4512_implies_Equation4268 G h310 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation311 G)) : AssociativeTheory34 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h311, h4512⟩

private theorem AT168_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation312 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation312_4512_implies_Equation307 G h312 h4512
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h308 := Equation3258_4283_4512_implies_Equation308 G h3258 h4283 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation313 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation313_4512_implies_Equation40 G h313 h4512
  have h309 := Equation313_4512_implies_Equation309 G h313 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation314 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation314_4512_implies_Equation40 G h314 h4512
  have h311 := Equation314_4512_implies_Equation311 G h314 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT168_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation315 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation315_4512_implies_Equation307 G h315 h4512
  have h3278 := Equation315_4512_implies_Equation3278 G h315 h4512
  have h4272 := Equation315_4512_implies_Equation4272 G h315 h4512
  have h4284 := Equation315_4512_implies_Equation4284 G h315 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h4269 := Equation4270_4314_4512_implies_Equation4269 G h4270 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation316 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation316_4512_implies_Equation40 G h316 h4512
  have h307 := Equation316_4512_implies_Equation307 G h316 h4512
  have h4268 := Equation316_4512_implies_Equation4268 G h316 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation318 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h309 := Equation318_4512_implies_Equation309 G h318 h4512
  have h3278 := Equation318_4512_implies_Equation3278 G h318 h4512
  have h4269 := Equation318_4512_implies_Equation4269 G h318 h4512
  have h4287 := Equation318_4512_implies_Equation4287 G h318 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT168_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation323 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation323_4512_implies_Equation307 G h323 h4512
  have h3306 := Equation323_4512_implies_Equation3306 G h323 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT168_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation325 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3316 := Equation325_4512_implies_Equation3316 G h325 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT168_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation326 G)) : AssociativeTheory165 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h326, h4283, h4512⟩

private theorem AT168_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation327 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  have h3255 := Equation327_4512_implies_Equation3255 G h327 h4512
  have h4314 := Equation327_4512_implies_Equation4314 G h327 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  have h3258 := Equation3255_4284_4512_implies_Equation3258 G h3255 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT168_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation329 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h326 := Equation329_4512_implies_Equation326 G h329 h4512
  have h3258 := Equation329_4512_implies_Equation3258 G h329 h4512
  have h4284 := Equation329_4512_implies_Equation4284 G h329 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT168_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation332 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h43 := Equation332_4512_implies_Equation43 G h332 h4512
  have h323 := Equation332_4512_implies_Equation323 G h332 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT168_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation333 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h323 := Equation333_4512_implies_Equation323 G h333 h4512
  have h4291 := Equation333_4512_implies_Equation4291 G h333 h4512
  have h4293 := Equation4283_4291_4512_implies_Equation4293 G h4283 h4291 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT168_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation343 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation343_4512_implies_Equation307 G h343 h4512
  have h312 := Equation343_4512_implies_Equation312 G h343 h4512
  have h323 := Equation343_4512_implies_Equation323 G h343 h4512
  have h3258 := Equation343_4512_implies_Equation3258 G h343 h4512
  have h3278 := Equation343_4512_implies_Equation3278 G h343 h4512
  have h3306 := Equation343_4512_implies_Equation3306 G h343 h4512
  have h4291 := Equation343_4512_implies_Equation4291 G h343 h4512
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

private theorem AT168_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation411 G)) : AssociativeTheory112 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  exact ⟨h8, h3308, h4512⟩

private theorem AT168_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation419 G)) : AssociativeTheory8 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3261 := Equation419_4512_implies_Equation3261 G h419 h4512
  have h3319 := Equation419_4512_implies_Equation3319 G h419 h4512
  have h3256 := Equation3261_4283_4512_implies_Equation3256 G h3261 h4283 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  exact ⟨h11, h4512⟩

private theorem AT168_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation429 G)) : AssociativeTheory8 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3306 := Equation429_4512_implies_Equation3306 G h429 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  exact ⟨h11, h4512⟩

private theorem AT168_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation440 G)) : AssociativeTheory8 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  exact ⟨h11, h4512⟩

private theorem AT168_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation477 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  have h513 := Equation477_4512_implies_Equation513 G h477 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT168_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation504 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h513 := Equation504_4512_implies_Equation513 G h504 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT168_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation513 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h43 := Equation513_4283_4512_implies_Equation43 G h513 h4283 h4512
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h4290 := Equation43_4512_implies_Equation4290 G h43 h4512
  have h440 := Equation513_4290_4512_implies_Equation440 G h513 h4290 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT168_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3253 G)) : AssociativeTheory168 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT168_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3255 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h308 := Equation3255_4283_4512_implies_Equation308 G h3255 h4283 h4512
  have h307 := Equation3255_4512_implies_Equation307 G h3255 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3256 G)) : AssociativeTheory169 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3256, h4283, h4512⟩

private theorem AT168_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3258 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h308 := Equation3258_4283_4512_implies_Equation308 G h3258 h4283 h4512
  have h307 := Equation3258_4512_implies_Equation307 G h3258 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3259 G)) : AssociativeTheory169 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  exact ⟨h3256, h4283, h4512⟩

private theorem AT168_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3260 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3260_4512_implies_Equation307 G h3260 h4512
  have h308 := Equation3260_4512_implies_Equation308 G h3260 h4512
  have h4268 := Equation3260_4512_implies_Equation4268 G h3260 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3261 G)) : AssociativeTheory169 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3256 := Equation3261_4283_4512_implies_Equation3256 G h3261 h4283 h4512
  exact ⟨h3256, h4283, h4512⟩

private theorem AT168_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3264 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3264_4512_implies_Equation307 G h3264 h4512
  have h3255 := Equation3264_4512_implies_Equation3255 G h3264 h4512
  have h308 := Equation3255_4283_4512_implies_Equation308 G h3255 h4283 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3265 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3265_4512_implies_Equation307 G h3265 h4512
  have h308 := Equation3265_4512_implies_Equation308 G h3265 h4512
  have h4268 := Equation3265_4512_implies_Equation4268 G h3265 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3267 G)) : AssociativeTheory92 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3267_4512_implies_Equation307 G h3267 h4512
  have h4268 := Equation3267_4512_implies_Equation4268 G h3267 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h3267, h4512⟩

private theorem AT168_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3271 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h4275 := Equation3271_4512_implies_Equation4275 G h3271 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3273 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3273_4512_implies_Equation40 G h3273 h4512
  have h307 := Equation3273_4512_implies_Equation307 G h3273 h4512
  have h4268 := Equation3273_4512_implies_Equation4268 G h3273 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3274 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3274_4512_implies_Equation307 G h3274 h4512
  have h3278 := Equation3274_4512_implies_Equation3278 G h3274 h4512
  have h4272 := Equation3274_4512_implies_Equation4272 G h3274 h4512
  have h4284 := Equation3274_4512_implies_Equation4284 G h3274 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h4269 := Equation4270_4314_4512_implies_Equation4269 G h4270 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3275 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3275_4512_implies_Equation40 G h3275 h4512
  have h307 := Equation3275_4512_implies_Equation307 G h3275 h4512
  have h4268 := Equation3275_4512_implies_Equation4268 G h3275 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3277 G)) : AssociativeTheory93 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3277_4512_implies_Equation40 G h3277 h4512
  have h307 := Equation3277_4512_implies_Equation307 G h3277 h4512
  have h3267 := Equation3277_4512_implies_Equation3267 G h3277 h4512
  have h4268 := Equation3277_4512_implies_Equation4268 G h3277 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h3267, h4512⟩

private theorem AT168_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3278 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4275 := Equation40_4512_implies_Equation4275 G h40 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3290 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3290_4512_implies_Equation40 G h3290 h4512
  have h307 := Equation3290_4512_implies_Equation307 G h3290 h4512
  have h4268 := Equation3290_4512_implies_Equation4268 G h3290 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3292 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3292_4512_implies_Equation307 G h3292 h4512
  have h3278 := Equation3292_4512_implies_Equation3278 G h3292 h4512
  have h4272 := Equation3292_4512_implies_Equation4272 G h3292 h4512
  have h4284 := Equation3292_4512_implies_Equation4284 G h3292 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h4269 := Equation4270_4314_4512_implies_Equation4269 G h4270 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3300 G)) : AssociativeTheory93 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3300_4512_implies_Equation307 G h3300 h4512
  have h3278 := Equation3300_4512_implies_Equation3278 G h3300 h4512
  have h4272 := Equation3300_4512_implies_Equation4272 G h3300 h4512
  have h4284 := Equation3300_4512_implies_Equation4284 G h3300 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h3267 := Equation40_3300_4512_implies_Equation3267 G h40 h3300 h4512
  have h4269 := Equation4270_4314_4512_implies_Equation4269 G h4270 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h3267, h4512⟩

private theorem AT168_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3306 G)) : AssociativeTheory111 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  exact ⟨h3308, h4512⟩

private theorem AT168_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3308 G)) : AssociativeTheory111 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3308, h4512⟩

private theorem AT168_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3309 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h323 := Equation3309_4512_implies_Equation323 G h3309 h4512
  have h326 := Equation3309_4512_implies_Equation326 G h3309 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT168_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3315 G)) : AssociativeTheory111 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3306 := Equation3315_4283_4512_implies_Equation3306 G h3315 h4283 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  exact ⟨h3308, h4512⟩

private theorem AT168_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3316 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h3316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h307 := Equation3316_4512_implies_Equation307 G h3316 h4512
  have h3306 := Equation323_4512_implies_Equation3306 G h323 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT168_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3319 G)) : AssociativeTheory170 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3319, h4283, h4512⟩

private theorem AT168_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3322 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3322_4512_implies_Equation307 G h3322 h4512
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  have h3316 := Equation3322_4512_implies_Equation3316 G h3322 h4512
  have h3319 := Equation3322_4512_implies_Equation3319 G h3322 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h308 := Equation3255_4283_4512_implies_Equation308 G h3255 h4283 h4512
  have h309 := Equation323_3255_4512_implies_Equation309 G h323 h3255 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT168_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3323 G)) : AssociativeTheory107 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  have h3306 := Equation3315_4283_4512_implies_Equation3306 G h3315 h4283 h4512
  exact ⟨h3256, h3306, h4512⟩

private theorem AT168_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3326 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3326_4512_implies_Equation307 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  have h3306 := Equation3326_4512_implies_Equation3306 G h3326 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT168_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3331 G)) : AssociativeTheory107 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3256 := Equation3331_4512_implies_Equation3256 G h3331 h4512
  have h3306 := Equation3331_4512_implies_Equation3306 G h3331 h4512
  exact ⟨h3256, h3306, h4512⟩

private theorem AT168_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3334 G)) : AssociativeTheory107 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h3306 := Equation3334_4512_implies_Equation3306 G h3334 h4512
  have h3256 := Equation3261_4283_4512_implies_Equation3256 G h3261 h4283 h4512
  exact ⟨h3256, h3306, h4512⟩

private theorem AT168_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3342 G)) : AssociativeTheory106 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h43 := Equation3342_4512_implies_Equation43 G h3342 h4512
  have h3306 := Equation3342_4512_implies_Equation3306 G h3342 h4512
  exact ⟨h43, h3306, h4512⟩

private theorem AT168_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3346 G)) : AssociativeTheory106 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3306 := Equation3346_4512_implies_Equation3306 G h3346 h4512
  have h4320 := Equation3346_4512_implies_Equation4320 G h3346 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h43 := Equation3306_4290_4512_implies_Equation43 G h3306 h4290 h4512
  exact ⟨h43, h3306, h4512⟩

private theorem AT168_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3350 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3350_4512_implies_Equation40 G h3350 h4512
  have h3306 := Equation3350_4512_implies_Equation3306 G h3350 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT168_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3353 G)) : AssociativeTheory106 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3306 := Equation3353_4512_implies_Equation3306 G h3353 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h43 := Equation3315_3353_4512_implies_Equation43 G h3315 h3353 h4512
  exact ⟨h43, h3306, h4512⟩

private theorem AT168_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3388 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3278 := Equation3388_4512_implies_Equation3278 G h3388 h4512
  have h3306 := Equation3388_4512_implies_Equation3306 G h3388 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT168_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation3414 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h3306 := Equation3414_4512_implies_Equation3306 G h3414 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT168_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4268 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4269 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4269_4512_implies_Equation307 G h3253 h4269 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4270 G)) : AssociativeTheory169 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  exact ⟨h3256, h4283, h4512⟩

private theorem AT168_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4271 G)) : AssociativeTheory34 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4271_4512_implies_Equation4269 G h4271 h4512
  have h4314 := Equation4271_4512_implies_Equation4314 G h4271 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h311, h4512⟩

private theorem AT168_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4272 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h4280 := Equation4270_4272_4512_implies_Equation4280 G h4270 h4272 h4512
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h4343 := Equation4280_4512_implies_Equation4343 G h4280 h4512
  have h4284 := Equation307_4283_4343_4512_implies_Equation4284 G h307 h4283 h4343 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4273 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4274 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4268 := Equation4274_4512_implies_Equation4268 G h4274 h4512
  have h4269 := Equation4274_4512_implies_Equation4269 G h4274 h4512
  have h4273 := Equation4274_4512_implies_Equation4273 G h4274 h4512
  have h4315 := Equation4274_4512_implies_Equation4315 G h4274 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT168_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4275 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4276 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h4275 := Equation40_4512_implies_Equation4275 G h40 h4512
  have h4268 := Equation4275_4276_4512_implies_Equation4268 G h4275 h4276 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4277 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4268 := Equation4277_4512_implies_Equation4268 G h4277 h4512
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h4293 := Equation4277_4512_implies_Equation4293 G h4277 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h307 := Equation3253_4293_4512_implies_Equation307 G h3253 h4293 h4512
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4278 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4278_4512_implies_Equation4269 G h4278 h4512
  have h4275 := Equation4278_4512_implies_Equation4275 G h4278 h4512
  have h4287 := Equation4278_4512_implies_Equation4287 G h4278 h4512
  have h4291 := Equation4278_4512_implies_Equation4291 G h4278 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT168_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4279 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4279_4512_implies_Equation4269 G h4279 h4512
  have h4273 := Equation4279_4512_implies_Equation4273 G h4279 h4512
  have h4321 := Equation4279_4512_implies_Equation4321 G h4279 h4512
  have h307 := Equation3253_4321_4512_implies_Equation307 G h3253 h4321 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4280 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4270 := Equation4280_4512_implies_Equation4270 G h4280 h4512
  have h4272 := Equation4280_4512_implies_Equation4272 G h4280 h4512
  have h4276 := Equation4280_4512_implies_Equation4276 G h4280 h4512
  have h4343 := Equation4280_4512_implies_Equation4343 G h4280 h4512
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h4284 := Equation307_4283_4343_4512_implies_Equation4284 G h307 h4283 h4343 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4283 G)) : AssociativeTheory168 G := by
  obtain ⟨hh, h4283⟩ := h
  exact hh

private theorem AT168_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4284 G)) : AssociativeTheory183 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  exact ⟨h307, h4283, h4284, h4512⟩

private theorem AT168_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4286 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4287 G)) : AssociativeTheory34 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4287_4512_implies_Equation4269 G h4287 h4512
  have h4284 := Equation4287_4512_implies_Equation4284 G h4287 h4512
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h311, h4512⟩

private theorem AT168_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4288 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4290 G)) : AssociativeTheory196 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3253, h4283, h4290, h4512⟩

private theorem AT168_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4291 G)) : AssociativeTheory213 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  exact ⟨h307, h4283, h4291, h4512⟩

private theorem AT168_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4293 G)) : AssociativeTheory213 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4293_4512_implies_Equation307 G h3253 h4293 h4512
  have h4291 := Equation4283_4293_4512_implies_Equation4291 G h4283 h4293 h4512
  exact ⟨h307, h4283, h4291, h4512⟩

private theorem AT168_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4296 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4296_4512_implies_Equation4269 G h4296 h4512
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  have h4291 := Equation4296_4512_implies_Equation4291 G h4296 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4297 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4275 := Equation4297_4512_implies_Equation4275 G h4297 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4299 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4268 := Equation4299_4512_implies_Equation4268 G h4299 h4512
  have h4276 := Equation4299_4512_implies_Equation4276 G h4299 h4512
  have h4293 := Equation4299_4512_implies_Equation4293 G h4299 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h307 := Equation3253_4293_4512_implies_Equation307 G h3253 h4293 h4512
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4300 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4272 := Equation4300_4512_implies_Equation4272 G h4300 h4512
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  have h4268 := Equation4270_4300_4512_implies_Equation4268 G h4270 h4300 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h3278 := Equation312_4512_implies_Equation3278 G h312 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4278 := Equation4269_4300_4512_implies_Equation4278 G h4269 h4300 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4287 := Equation4278_4512_implies_Equation4287 G h4278 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT168_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4301 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4301_4512_implies_Equation4269 G h4301 h4512
  have h4273 := Equation4301_4512_implies_Equation4273 G h4301 h4512
  have h4291 := Equation4301_4512_implies_Equation4291 G h4301 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4304 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h4275 := Equation4304_4512_implies_Equation4275 G h4304 h4512
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h4270 := Equation4272_4283_4512_implies_Equation4270 G h4272 h4283 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h4269 := Equation4270_4314_4512_implies_Equation4269 G h4270 h4314 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4305 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4314 G)) : AssociativeTheory183 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  exact ⟨h307, h4283, h4284, h4512⟩

private theorem AT168_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4315 G)) : AssociativeTheory34 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4268 := Equation4315_4512_implies_Equation4268 G h4315 h4512
  have h4314 := Equation4315_4512_implies_Equation4314 G h4315 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h4269 := Equation4268_4283_4512_implies_Equation4269 G h4268 h4283 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h311, h4512⟩

private theorem AT168_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4318 G)) : AssociativeTheory32 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  have h307 := Equation3253_4269_4512_implies_Equation307 G h3253 h4269 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h308, h309, h4512⟩

private theorem AT168_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4320 G)) : AssociativeTheory196 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  exact ⟨h3253, h4283, h4290, h4512⟩

private theorem AT168_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4321 G)) : AssociativeTheory213 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4321_4512_implies_Equation307 G h3253 h4321 h4512
  have h4291 := Equation4283_4321_4512_implies_Equation4291 G h4283 h4321 h4512
  exact ⟨h307, h4283, h4291, h4512⟩

private theorem AT168_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4325 G)) : AssociativeTheory146 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h4273, h4512⟩

private theorem AT168_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4327 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4320 := Equation4327_4512_implies_Equation4320 G h4327 h4512
  have h307 := Equation3253_4269_4512_implies_Equation307 G h3253 h4269 h4512
  have h4290 := Equation4283_4320_4512_implies_Equation4290 G h4283 h4320 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4331 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h4269 := Equation4331_4512_implies_Equation4269 G h4331 h4512
  have h4273 := Equation4331_4512_implies_Equation4273 G h4331 h4512
  have h4314 := Equation4331_4512_implies_Equation4314 G h4331 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT168_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4343 G)) : AssociativeTheory203 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  have h307 := Equation3253_4343_4512_implies_Equation307 G h3253 h4343 h4512
  have h4284 := Equation307_4283_4343_4512_implies_Equation4284 G h307 h4283 h4343 h4512
  have h4290 := Equation4284_4343_4512_implies_Equation4290 G h4284 h4343 h4512
  exact ⟨h307, h4283, h4284, h4290, h4512⟩

private theorem AT168_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4358 G)) : AssociativeTheory317 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3253, h4358, h4512⟩

private theorem AT168_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4362 G)) : AssociativeTheory379 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3253, h4283, h4362, h4512⟩

private theorem AT168_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4364 G)) : AssociativeTheory412 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3253, h4364, h4512⟩

private theorem AT168_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4369 G)) : AssociativeTheory438 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at168
  obtain ⟨h1, h3253, h4283, h4512⟩ := g hh
  exact ⟨h3253, h4283, h4369, h4512⟩

private theorem AT168_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory168 G) ∧ (Equation4512 G)) : AssociativeTheory168 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT168_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj168 eqid)) : (AssociativeTheory168 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj168 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at168 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT168_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory168 G) ∧ (EQeq G eqid) <-> (ATearly G (conj168 eqid)) :=
⟨match eqid with
| eq1 => AT168_Equation1_implies G
| eq2 => AT168_Equation2_implies G
| eq3 => AT168_Equation3_implies G
| eq4 => AT168_Equation4_implies G
| eq5 => AT168_Equation5_implies G
| eq8 => AT168_Equation8_implies G
| eq10 => AT168_Equation10_implies G
| eq11 => AT168_Equation11_implies G
| eq14 => AT168_Equation14_implies G
| eq16 => AT168_Equation16_implies G
| eq38 => AT168_Equation38_implies G
| eq39 => AT168_Equation39_implies G
| eq40 => AT168_Equation40_implies G
| eq41 => AT168_Equation41_implies G
| eq43 => AT168_Equation43_implies G
| eq47 => AT168_Equation47_implies G
| eq56 => AT168_Equation56_implies G
| eq66 => AT168_Equation66_implies G
| eq75 => AT168_Equation75_implies G
| eq307 => AT168_Equation307_implies G
| eq308 => AT168_Equation308_implies G
| eq309 => AT168_Equation309_implies G
| eq310 => AT168_Equation310_implies G
| eq311 => AT168_Equation311_implies G
| eq312 => AT168_Equation312_implies G
| eq313 => AT168_Equation313_implies G
| eq314 => AT168_Equation314_implies G
| eq315 => AT168_Equation315_implies G
| eq316 => AT168_Equation316_implies G
| eq318 => AT168_Equation318_implies G
| eq323 => AT168_Equation323_implies G
| eq325 => AT168_Equation325_implies G
| eq326 => AT168_Equation326_implies G
| eq327 => AT168_Equation327_implies G
| eq329 => AT168_Equation329_implies G
| eq332 => AT168_Equation332_implies G
| eq333 => AT168_Equation333_implies G
| eq343 => AT168_Equation343_implies G
| eq411 => AT168_Equation411_implies G
| eq419 => AT168_Equation419_implies G
| eq429 => AT168_Equation429_implies G
| eq440 => AT168_Equation440_implies G
| eq477 => AT168_Equation477_implies G
| eq504 => AT168_Equation504_implies G
| eq513 => AT168_Equation513_implies G
| eq3253 => AT168_Equation3253_implies G
| eq3255 => AT168_Equation3255_implies G
| eq3256 => AT168_Equation3256_implies G
| eq3258 => AT168_Equation3258_implies G
| eq3259 => AT168_Equation3259_implies G
| eq3260 => AT168_Equation3260_implies G
| eq3261 => AT168_Equation3261_implies G
| eq3264 => AT168_Equation3264_implies G
| eq3265 => AT168_Equation3265_implies G
| eq3267 => AT168_Equation3267_implies G
| eq3271 => AT168_Equation3271_implies G
| eq3273 => AT168_Equation3273_implies G
| eq3274 => AT168_Equation3274_implies G
| eq3275 => AT168_Equation3275_implies G
| eq3277 => AT168_Equation3277_implies G
| eq3278 => AT168_Equation3278_implies G
| eq3290 => AT168_Equation3290_implies G
| eq3292 => AT168_Equation3292_implies G
| eq3300 => AT168_Equation3300_implies G
| eq3306 => AT168_Equation3306_implies G
| eq3308 => AT168_Equation3308_implies G
| eq3309 => AT168_Equation3309_implies G
| eq3315 => AT168_Equation3315_implies G
| eq3316 => AT168_Equation3316_implies G
| eq3319 => AT168_Equation3319_implies G
| eq3322 => AT168_Equation3322_implies G
| eq3323 => AT168_Equation3323_implies G
| eq3326 => AT168_Equation3326_implies G
| eq3331 => AT168_Equation3331_implies G
| eq3334 => AT168_Equation3334_implies G
| eq3342 => AT168_Equation3342_implies G
| eq3346 => AT168_Equation3346_implies G
| eq3350 => AT168_Equation3350_implies G
| eq3353 => AT168_Equation3353_implies G
| eq3388 => AT168_Equation3388_implies G
| eq3414 => AT168_Equation3414_implies G
| eq4268 => AT168_Equation4268_implies G
| eq4269 => AT168_Equation4269_implies G
| eq4270 => AT168_Equation4270_implies G
| eq4271 => AT168_Equation4271_implies G
| eq4272 => AT168_Equation4272_implies G
| eq4273 => AT168_Equation4273_implies G
| eq4274 => AT168_Equation4274_implies G
| eq4275 => AT168_Equation4275_implies G
| eq4276 => AT168_Equation4276_implies G
| eq4277 => AT168_Equation4277_implies G
| eq4278 => AT168_Equation4278_implies G
| eq4279 => AT168_Equation4279_implies G
| eq4280 => AT168_Equation4280_implies G
| eq4283 => AT168_Equation4283_implies G
| eq4284 => AT168_Equation4284_implies G
| eq4286 => AT168_Equation4286_implies G
| eq4287 => AT168_Equation4287_implies G
| eq4288 => AT168_Equation4288_implies G
| eq4290 => AT168_Equation4290_implies G
| eq4291 => AT168_Equation4291_implies G
| eq4293 => AT168_Equation4293_implies G
| eq4296 => AT168_Equation4296_implies G
| eq4297 => AT168_Equation4297_implies G
| eq4299 => AT168_Equation4299_implies G
| eq4300 => AT168_Equation4300_implies G
| eq4301 => AT168_Equation4301_implies G
| eq4304 => AT168_Equation4304_implies G
| eq4305 => AT168_Equation4305_implies G
| eq4314 => AT168_Equation4314_implies G
| eq4315 => AT168_Equation4315_implies G
| eq4318 => AT168_Equation4318_implies G
| eq4320 => AT168_Equation4320_implies G
| eq4321 => AT168_Equation4321_implies G
| eq4325 => AT168_Equation4325_implies G
| eq4327 => AT168_Equation4327_implies G
| eq4331 => AT168_Equation4331_implies G
| eq4343 => AT168_Equation4343_implies G
| eq4358 => AT168_Equation4358_implies G
| eq4362 => AT168_Equation4362_implies G
| eq4364 => AT168_Equation4364_implies G
| eq4369 => AT168_Equation4369_implies G
| eq4512 => AT168_Equation4512_implies G
, AT168_conj_implied G eqid⟩

