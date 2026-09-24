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


def conj1 : EQIndex → ATIndex
| eq1 => at1
| eq2 => at2
| eq3 => at3
| eq4 => at4
| eq5 => at5
| eq8 => at6
| eq10 => at7
| eq11 => at8
| eq14 => at9
| eq16 => at10
| eq38 => at11
| eq39 => at12
| eq40 => at14
| eq41 => at13
| eq43 => at15
| eq47 => at19
| eq56 => at21
| eq66 => at22
| eq75 => at23
| eq307 => at25
| eq308 => at29
| eq309 => at30
| eq310 => at33
| eq311 => at34
| eq312 => at37
| eq313 => at31
| eq314 => at35
| eq315 => at39
| eq316 => at26
| eq318 => at40
| eq323 => at41
| eq325 => at45
| eq326 => at49
| eq327 => at47
| eq329 => at43
| eq332 => at42
| eq333 => at51
| eq343 => at44
| eq411 => at54
| eq419 => at56
| eq429 => at57
| eq440 => at58
| eq477 => at59
| eq504 => at60
| eq513 => at61
| eq3253 => at63
| eq3255 => at65
| eq3256 => at67
| eq3258 => at68
| eq3259 => at71
| eq3260 => at72
| eq3261 => at74
| eq3264 => at75
| eq3265 => at81
| eq3267 => at89
| eq3271 => at94
| eq3273 => at73
| eq3274 => at95
| eq3275 => at76
| eq3277 => at90
| eq3278 => at97
| eq3290 => at82
| eq3292 => at98
| eq3300 => at102
| eq3306 => at104
| eq3308 => at111
| eq3309 => at50
| eq3315 => at113
| eq3316 => at117
| eq3319 => at120
| eq3322 => at66
| eq3323 => at115
| eq3326 => at69
| eq3331 => at107
| eq3334 => at108
| eq3342 => at106
| eq3346 => at122
| eq3350 => at105
| eq3353 => at124
| eq3388 => at109
| eq3414 => at110
| eq4268 => at127
| eq4269 => at129
| eq4270 => at131
| eq4271 => at136
| eq4272 => at138
| eq4273 => at145
| eq4274 => at144
| eq4275 => at150
| eq4276 => at158
| eq4277 => at151
| eq4278 => at160
| eq4279 => at148
| eq4280 => at142
| eq4283 => at161
| eq4284 => at174
| eq4286 => at130
| eq4287 => at185
| eq4288 => at133
| eq4290 => at187
| eq4291 => at205
| eq4293 => at222
| eq4296 => at152
| eq4297 => at153
| eq4299 => at139
| eq4300 => at228
| eq4301 => at147
| eq4304 => at154
| eq4305 => at156
| eq4314 => at230
| eq4315 => at239
| eq4318 => at134
| eq4320 => at241
| eq4321 => at263
| eq4325 => at149
| eq4327 => at140
| eq4331 => at143
| eq4343 => at285
| eq4358 => at306
| eq4362 => at351
| eq4364 => at408
| eq4369 => at420
| eq4512 => at1


private theorem AT1_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation1 G)) : AssociativeTheory1 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT1_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT1_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3, h4512⟩

private theorem AT1_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4, h4512⟩

private theorem AT1_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation5 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h5, h4512⟩

private theorem AT1_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation8 G)) : AssociativeTheory6 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h8, h4512⟩

private theorem AT1_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation10 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h10, h4512⟩

private theorem AT1_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation11 G)) : AssociativeTheory8 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h11, h4512⟩

private theorem AT1_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation14 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h14, h4512⟩

private theorem AT1_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation16 G)) : AssociativeTheory10 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h16, h4512⟩

private theorem AT1_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation38 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h38, h4512⟩

private theorem AT1_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation39 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h39, h4512⟩

private theorem AT1_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation40 G)) : AssociativeTheory14 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h40, h4512⟩

private theorem AT1_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h38 := Equation41_4512_implies_Equation38 G h41 h4512
  have h39 := Equation41_4512_implies_Equation39 G h41 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT1_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation43 G)) : AssociativeTheory15 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h43, h4512⟩

private theorem AT1_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation47 G)) : AssociativeTheory19 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h47, h4512⟩

private theorem AT1_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation56 G)) : AssociativeTheory21 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h56, h4512⟩

private theorem AT1_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation66 G)) : AssociativeTheory22 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h43 := Equation66_4512_implies_Equation43 G h66 h4512
  have h56 := Equation66_4512_implies_Equation56 G h66 h4512
  exact ⟨h43, h56, h4512⟩

private theorem AT1_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation75 G)) : AssociativeTheory23 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h75, h4512⟩

private theorem AT1_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation307 G)) : AssociativeTheory25 G := by
  obtain ⟨hh, h307⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h307, h4512⟩

private theorem AT1_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation308 G)) : AssociativeTheory29 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h308, h4512⟩

private theorem AT1_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation309 G)) : AssociativeTheory30 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h309, h4512⟩

private theorem AT1_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation310 G)) : AssociativeTheory33 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h310, h4512⟩

private theorem AT1_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation311 G)) : AssociativeTheory34 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h311, h4512⟩

private theorem AT1_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation312 G)) : AssociativeTheory37 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h312, h4512⟩

private theorem AT1_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation313 G)) : AssociativeTheory31 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation313_4512_implies_Equation40 G h313 h4512
  have h309 := Equation313_4512_implies_Equation309 G h313 h4512
  exact ⟨h40, h309, h4512⟩

private theorem AT1_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation314 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation314_4512_implies_Equation40 G h314 h4512
  have h311 := Equation314_4512_implies_Equation311 G h314 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT1_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation315 G)) : AssociativeTheory39 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h315, h4512⟩

private theorem AT1_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation316 G)) : AssociativeTheory26 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation316_4512_implies_Equation40 G h316 h4512
  have h307 := Equation316_4512_implies_Equation307 G h316 h4512
  exact ⟨h40, h307, h4512⟩

private theorem AT1_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation318 G)) : AssociativeTheory40 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h318, h4512⟩

private theorem AT1_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation323 G)) : AssociativeTheory41 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h323, h4512⟩

private theorem AT1_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation325 G)) : AssociativeTheory45 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h325, h4512⟩

private theorem AT1_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation326 G)) : AssociativeTheory49 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h326, h4512⟩

private theorem AT1_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation327 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h308 := Equation327_4512_implies_Equation308 G h327 h4512
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT1_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation329 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h309 := Equation329_4512_implies_Equation309 G h329 h4512
  have h323 := Equation329_4512_implies_Equation323 G h329 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT1_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation332 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h43 := Equation332_4512_implies_Equation43 G h332 h4512
  have h323 := Equation332_4512_implies_Equation323 G h332 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT1_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation333 G)) : AssociativeTheory51 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h333, h4512⟩

private theorem AT1_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation343 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h312 := Equation343_4512_implies_Equation312 G h343 h4512
  have h323 := Equation343_4512_implies_Equation323 G h343 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT1_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation411 G)) : AssociativeTheory54 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h411, h4512⟩

private theorem AT1_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation419 G)) : AssociativeTheory56 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h419, h4512⟩

private theorem AT1_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation429 G)) : AssociativeTheory57 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h429, h4512⟩

private theorem AT1_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation440 G)) : AssociativeTheory58 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h440, h4512⟩

private theorem AT1_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation477 G)) : AssociativeTheory59 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h43 := Equation477_4512_implies_Equation43 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  exact ⟨h43, h440, h4512⟩

private theorem AT1_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation504 G)) : AssociativeTheory60 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h504, h4512⟩

private theorem AT1_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation513 G)) : AssociativeTheory61 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h513, h4512⟩

private theorem AT1_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3253 G)) : AssociativeTheory63 G := by
  obtain ⟨hh, h3253⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3253, h4512⟩

private theorem AT1_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3255 G)) : AssociativeTheory65 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3255, h4512⟩

private theorem AT1_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3256 G)) : AssociativeTheory67 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3256, h4512⟩

private theorem AT1_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3258 G)) : AssociativeTheory68 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3258, h4512⟩

private theorem AT1_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3259 G)) : AssociativeTheory71 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3259, h4512⟩

private theorem AT1_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3260 G)) : AssociativeTheory72 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3260, h4512⟩

private theorem AT1_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3261 G)) : AssociativeTheory74 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3261, h4512⟩

private theorem AT1_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3264 G)) : AssociativeTheory75 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3264, h4512⟩

private theorem AT1_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3265 G)) : AssociativeTheory81 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3265, h4512⟩

private theorem AT1_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3267 G)) : AssociativeTheory89 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3267, h4512⟩

private theorem AT1_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3271 G)) : AssociativeTheory94 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3271, h4512⟩

private theorem AT1_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3273 G)) : AssociativeTheory73 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation3273_4512_implies_Equation40 G h3273 h4512
  have h3260 := Equation3273_4512_implies_Equation3260 G h3273 h4512
  exact ⟨h40, h3260, h4512⟩

private theorem AT1_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3274 G)) : AssociativeTheory95 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3274, h4512⟩

private theorem AT1_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3275 G)) : AssociativeTheory76 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation3275_4512_implies_Equation40 G h3275 h4512
  have h3264 := Equation3275_4512_implies_Equation3264 G h3275 h4512
  exact ⟨h40, h3264, h4512⟩

private theorem AT1_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3277 G)) : AssociativeTheory90 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation3277_4512_implies_Equation40 G h3277 h4512
  have h3267 := Equation3277_4512_implies_Equation3267 G h3277 h4512
  exact ⟨h40, h3267, h4512⟩

private theorem AT1_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3278 G)) : AssociativeTheory97 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3278, h4512⟩

private theorem AT1_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3290 G)) : AssociativeTheory82 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation3290_4512_implies_Equation40 G h3290 h4512
  have h3265 := Equation3290_4512_implies_Equation3265 G h3290 h4512
  exact ⟨h40, h3265, h4512⟩

private theorem AT1_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3292 G)) : AssociativeTheory98 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3292, h4512⟩

private theorem AT1_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3300 G)) : AssociativeTheory102 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3300, h4512⟩

private theorem AT1_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3306 G)) : AssociativeTheory104 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3306, h4512⟩

private theorem AT1_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3308 G)) : AssociativeTheory111 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3308, h4512⟩

private theorem AT1_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3309 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h323 := Equation3309_4512_implies_Equation323 G h3309 h4512
  have h326 := Equation3309_4512_implies_Equation326 G h3309 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT1_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3315 G)) : AssociativeTheory113 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3315, h4512⟩

private theorem AT1_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3316 G)) : AssociativeTheory117 G := by
  obtain ⟨hh, h3316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3316, h4512⟩

private theorem AT1_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3319 G)) : AssociativeTheory120 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3319, h4512⟩

private theorem AT1_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3322 G)) : AssociativeTheory66 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h326 := Equation3322_4512_implies_Equation326 G h3322 h4512
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  exact ⟨h326, h3255, h4512⟩

private theorem AT1_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3323 G)) : AssociativeTheory115 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  exact ⟨h3256, h3315, h4512⟩

private theorem AT1_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3326 G)) : AssociativeTheory69 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h323 := Equation3326_4512_implies_Equation323 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  exact ⟨h323, h3258, h4512⟩

private theorem AT1_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3331 G)) : AssociativeTheory107 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h3256 := Equation3331_4512_implies_Equation3256 G h3331 h4512
  have h3306 := Equation3331_4512_implies_Equation3306 G h3331 h4512
  exact ⟨h3256, h3306, h4512⟩

private theorem AT1_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3334 G)) : AssociativeTheory108 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h3306 := Equation3334_4512_implies_Equation3306 G h3334 h4512
  exact ⟨h3261, h3306, h4512⟩

private theorem AT1_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3342 G)) : AssociativeTheory106 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h43 := Equation3342_4512_implies_Equation43 G h3342 h4512
  have h3306 := Equation3342_4512_implies_Equation3306 G h3342 h4512
  exact ⟨h43, h3306, h4512⟩

private theorem AT1_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3346 G)) : AssociativeTheory122 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3346, h4512⟩

private theorem AT1_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3350 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h40 := Equation3350_4512_implies_Equation40 G h3350 h4512
  have h3306 := Equation3350_4512_implies_Equation3306 G h3350 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT1_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3353 G)) : AssociativeTheory124 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h3353, h4512⟩

private theorem AT1_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3388 G)) : AssociativeTheory109 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h3271 := Equation3388_4512_implies_Equation3271 G h3388 h4512
  have h3306 := Equation3388_4512_implies_Equation3306 G h3388 h4512
  exact ⟨h3271, h3306, h4512⟩

private theorem AT1_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation3414 G)) : AssociativeTheory110 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h3306 := Equation3414_4512_implies_Equation3306 G h3414 h4512
  exact ⟨h3278, h3306, h4512⟩

private theorem AT1_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4268 G)) : AssociativeTheory127 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4268, h4512⟩

private theorem AT1_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4269 G)) : AssociativeTheory129 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4269, h4512⟩

private theorem AT1_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4270 G)) : AssociativeTheory131 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4270, h4512⟩

private theorem AT1_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4271 G)) : AssociativeTheory136 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4271, h4512⟩

private theorem AT1_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4272 G)) : AssociativeTheory138 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4272, h4512⟩

private theorem AT1_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4273 G)) : AssociativeTheory145 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4273, h4512⟩

private theorem AT1_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4274 G)) : AssociativeTheory144 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4271 := Equation4274_4512_implies_Equation4271 G h4274 h4512
  have h4272 := Equation4274_4512_implies_Equation4272 G h4274 h4512
  exact ⟨h4271, h4272, h4512⟩

private theorem AT1_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4275 G)) : AssociativeTheory150 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4275, h4512⟩

private theorem AT1_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4276 G)) : AssociativeTheory158 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4276, h4512⟩

private theorem AT1_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4277 G)) : AssociativeTheory151 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4268 := Equation4277_4512_implies_Equation4268 G h4277 h4512
  have h4275 := Equation4277_4512_implies_Equation4275 G h4277 h4512
  exact ⟨h4268, h4275, h4512⟩

private theorem AT1_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4278 G)) : AssociativeTheory160 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4278, h4512⟩

private theorem AT1_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4279 G)) : AssociativeTheory148 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4269 := Equation4279_4512_implies_Equation4269 G h4279 h4512
  have h4273 := Equation4279_4512_implies_Equation4273 G h4279 h4512
  exact ⟨h4269, h4273, h4512⟩

private theorem AT1_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4280 G)) : AssociativeTheory142 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4270 := Equation4280_4512_implies_Equation4270 G h4280 h4512
  have h4272 := Equation4280_4512_implies_Equation4272 G h4280 h4512
  exact ⟨h4270, h4272, h4512⟩

private theorem AT1_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4283 G)) : AssociativeTheory161 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4283, h4512⟩

private theorem AT1_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4284 G)) : AssociativeTheory174 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4284, h4512⟩

private theorem AT1_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4286 G)) : AssociativeTheory130 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  exact ⟨h4268, h4269, h4512⟩

private theorem AT1_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4287 G)) : AssociativeTheory185 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4287, h4512⟩

private theorem AT1_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4288 G)) : AssociativeTheory133 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4270 := Equation4288_4512_implies_Equation4270 G h4288 h4512
  exact ⟨h4268, h4270, h4512⟩

private theorem AT1_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4290 G)) : AssociativeTheory187 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4290, h4512⟩

private theorem AT1_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4291 G)) : AssociativeTheory205 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4291, h4512⟩

private theorem AT1_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4293 G)) : AssociativeTheory222 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4293, h4512⟩

private theorem AT1_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4296 G)) : AssociativeTheory152 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4269 := Equation4296_4512_implies_Equation4269 G h4296 h4512
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  exact ⟨h4269, h4275, h4512⟩

private theorem AT1_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4297 G)) : AssociativeTheory153 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4270 := Equation4297_4512_implies_Equation4270 G h4297 h4512
  have h4275 := Equation4297_4512_implies_Equation4275 G h4297 h4512
  exact ⟨h4270, h4275, h4512⟩

private theorem AT1_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4299 G)) : AssociativeTheory139 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4268 := Equation4299_4512_implies_Equation4268 G h4299 h4512
  have h4272 := Equation4299_4512_implies_Equation4272 G h4299 h4512
  exact ⟨h4268, h4272, h4512⟩

private theorem AT1_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4300 G)) : AssociativeTheory228 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4300, h4512⟩

private theorem AT1_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4301 G)) : AssociativeTheory147 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4268 := Equation4301_4512_implies_Equation4268 G h4301 h4512
  have h4273 := Equation4301_4512_implies_Equation4273 G h4301 h4512
  exact ⟨h4268, h4273, h4512⟩

private theorem AT1_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4304 G)) : AssociativeTheory154 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h4275 := Equation4304_4512_implies_Equation4275 G h4304 h4512
  exact ⟨h4272, h4275, h4512⟩

private theorem AT1_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4305 G)) : AssociativeTheory156 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h4275 := Equation4305_4512_implies_Equation4275 G h4305 h4512
  exact ⟨h4273, h4275, h4512⟩

private theorem AT1_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4314 G)) : AssociativeTheory230 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4314, h4512⟩

private theorem AT1_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4315 G)) : AssociativeTheory239 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4315, h4512⟩

private theorem AT1_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4318 G)) : AssociativeTheory134 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4270 := Equation4318_4512_implies_Equation4270 G h4318 h4512
  exact ⟨h4269, h4270, h4512⟩

private theorem AT1_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4320 G)) : AssociativeTheory241 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4320, h4512⟩

private theorem AT1_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4321 G)) : AssociativeTheory263 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4321, h4512⟩

private theorem AT1_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4325 G)) : AssociativeTheory149 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4270 := Equation4325_4512_implies_Equation4270 G h4325 h4512
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  exact ⟨h4270, h4273, h4512⟩

private theorem AT1_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4327 G)) : AssociativeTheory140 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4272 := Equation4327_4512_implies_Equation4272 G h4327 h4512
  exact ⟨h4269, h4272, h4512⟩

private theorem AT1_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4331 G)) : AssociativeTheory143 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  have h4269 := Equation4331_4512_implies_Equation4269 G h4331 h4512
  have h4270 := Equation4331_4512_implies_Equation4270 G h4331 h4512
  have h4272 := Equation4331_4512_implies_Equation4272 G h4331 h4512
  exact ⟨h4269, h4270, h4272, h4512⟩

private theorem AT1_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4343 G)) : AssociativeTheory285 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4343, h4512⟩

private theorem AT1_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4358 G)) : AssociativeTheory306 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4358, h4512⟩

private theorem AT1_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4362 G)) : AssociativeTheory351 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4362, h4512⟩

private theorem AT1_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4364 G)) : AssociativeTheory408 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4364, h4512⟩

private theorem AT1_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4369 G)) : AssociativeTheory420 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at1
  obtain ⟨h1, h4512⟩ := g hh
  exact ⟨h4369, h4512⟩

private theorem AT1_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory1 G) ∧ (Equation4512 G)) : AssociativeTheory1 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT1_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj1 eqid)) : (AssociativeTheory1 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj1 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at1 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT1_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory1 G) ∧ (EQeq G eqid) <-> (ATearly G (conj1 eqid)) :=
⟨match eqid with
| eq1 => AT1_Equation1_implies G
| eq2 => AT1_Equation2_implies G
| eq3 => AT1_Equation3_implies G
| eq4 => AT1_Equation4_implies G
| eq5 => AT1_Equation5_implies G
| eq8 => AT1_Equation8_implies G
| eq10 => AT1_Equation10_implies G
| eq11 => AT1_Equation11_implies G
| eq14 => AT1_Equation14_implies G
| eq16 => AT1_Equation16_implies G
| eq38 => AT1_Equation38_implies G
| eq39 => AT1_Equation39_implies G
| eq40 => AT1_Equation40_implies G
| eq41 => AT1_Equation41_implies G
| eq43 => AT1_Equation43_implies G
| eq47 => AT1_Equation47_implies G
| eq56 => AT1_Equation56_implies G
| eq66 => AT1_Equation66_implies G
| eq75 => AT1_Equation75_implies G
| eq307 => AT1_Equation307_implies G
| eq308 => AT1_Equation308_implies G
| eq309 => AT1_Equation309_implies G
| eq310 => AT1_Equation310_implies G
| eq311 => AT1_Equation311_implies G
| eq312 => AT1_Equation312_implies G
| eq313 => AT1_Equation313_implies G
| eq314 => AT1_Equation314_implies G
| eq315 => AT1_Equation315_implies G
| eq316 => AT1_Equation316_implies G
| eq318 => AT1_Equation318_implies G
| eq323 => AT1_Equation323_implies G
| eq325 => AT1_Equation325_implies G
| eq326 => AT1_Equation326_implies G
| eq327 => AT1_Equation327_implies G
| eq329 => AT1_Equation329_implies G
| eq332 => AT1_Equation332_implies G
| eq333 => AT1_Equation333_implies G
| eq343 => AT1_Equation343_implies G
| eq411 => AT1_Equation411_implies G
| eq419 => AT1_Equation419_implies G
| eq429 => AT1_Equation429_implies G
| eq440 => AT1_Equation440_implies G
| eq477 => AT1_Equation477_implies G
| eq504 => AT1_Equation504_implies G
| eq513 => AT1_Equation513_implies G
| eq3253 => AT1_Equation3253_implies G
| eq3255 => AT1_Equation3255_implies G
| eq3256 => AT1_Equation3256_implies G
| eq3258 => AT1_Equation3258_implies G
| eq3259 => AT1_Equation3259_implies G
| eq3260 => AT1_Equation3260_implies G
| eq3261 => AT1_Equation3261_implies G
| eq3264 => AT1_Equation3264_implies G
| eq3265 => AT1_Equation3265_implies G
| eq3267 => AT1_Equation3267_implies G
| eq3271 => AT1_Equation3271_implies G
| eq3273 => AT1_Equation3273_implies G
| eq3274 => AT1_Equation3274_implies G
| eq3275 => AT1_Equation3275_implies G
| eq3277 => AT1_Equation3277_implies G
| eq3278 => AT1_Equation3278_implies G
| eq3290 => AT1_Equation3290_implies G
| eq3292 => AT1_Equation3292_implies G
| eq3300 => AT1_Equation3300_implies G
| eq3306 => AT1_Equation3306_implies G
| eq3308 => AT1_Equation3308_implies G
| eq3309 => AT1_Equation3309_implies G
| eq3315 => AT1_Equation3315_implies G
| eq3316 => AT1_Equation3316_implies G
| eq3319 => AT1_Equation3319_implies G
| eq3322 => AT1_Equation3322_implies G
| eq3323 => AT1_Equation3323_implies G
| eq3326 => AT1_Equation3326_implies G
| eq3331 => AT1_Equation3331_implies G
| eq3334 => AT1_Equation3334_implies G
| eq3342 => AT1_Equation3342_implies G
| eq3346 => AT1_Equation3346_implies G
| eq3350 => AT1_Equation3350_implies G
| eq3353 => AT1_Equation3353_implies G
| eq3388 => AT1_Equation3388_implies G
| eq3414 => AT1_Equation3414_implies G
| eq4268 => AT1_Equation4268_implies G
| eq4269 => AT1_Equation4269_implies G
| eq4270 => AT1_Equation4270_implies G
| eq4271 => AT1_Equation4271_implies G
| eq4272 => AT1_Equation4272_implies G
| eq4273 => AT1_Equation4273_implies G
| eq4274 => AT1_Equation4274_implies G
| eq4275 => AT1_Equation4275_implies G
| eq4276 => AT1_Equation4276_implies G
| eq4277 => AT1_Equation4277_implies G
| eq4278 => AT1_Equation4278_implies G
| eq4279 => AT1_Equation4279_implies G
| eq4280 => AT1_Equation4280_implies G
| eq4283 => AT1_Equation4283_implies G
| eq4284 => AT1_Equation4284_implies G
| eq4286 => AT1_Equation4286_implies G
| eq4287 => AT1_Equation4287_implies G
| eq4288 => AT1_Equation4288_implies G
| eq4290 => AT1_Equation4290_implies G
| eq4291 => AT1_Equation4291_implies G
| eq4293 => AT1_Equation4293_implies G
| eq4296 => AT1_Equation4296_implies G
| eq4297 => AT1_Equation4297_implies G
| eq4299 => AT1_Equation4299_implies G
| eq4300 => AT1_Equation4300_implies G
| eq4301 => AT1_Equation4301_implies G
| eq4304 => AT1_Equation4304_implies G
| eq4305 => AT1_Equation4305_implies G
| eq4314 => AT1_Equation4314_implies G
| eq4315 => AT1_Equation4315_implies G
| eq4318 => AT1_Equation4318_implies G
| eq4320 => AT1_Equation4320_implies G
| eq4321 => AT1_Equation4321_implies G
| eq4325 => AT1_Equation4325_implies G
| eq4327 => AT1_Equation4327_implies G
| eq4331 => AT1_Equation4331_implies G
| eq4343 => AT1_Equation4343_implies G
| eq4358 => AT1_Equation4358_implies G
| eq4362 => AT1_Equation4362_implies G
| eq4364 => AT1_Equation4364_implies G
| eq4369 => AT1_Equation4369_implies G
| eq4512 => AT1_Equation4512_implies G
, AT1_conj_implied G eqid⟩

