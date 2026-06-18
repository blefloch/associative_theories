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


def conj2 : EQIndex → ATIndex
| eq1 => at2
| eq2 => at2
| eq3 => at2
| eq4 => at2
| eq5 => at2
| eq8 => at2
| eq10 => at2
| eq11 => at2
| eq14 => at2
| eq16 => at2
| eq38 => at2
| eq39 => at2
| eq40 => at2
| eq41 => at2
| eq43 => at2
| eq47 => at2
| eq56 => at2
| eq66 => at2
| eq75 => at2
| eq307 => at2
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
| eq323 => at2
| eq325 => at2
| eq326 => at2
| eq327 => at2
| eq329 => at2
| eq332 => at2
| eq333 => at2
| eq343 => at2
| eq411 => at2
| eq419 => at2
| eq429 => at2
| eq440 => at2
| eq477 => at2
| eq504 => at2
| eq513 => at2
| eq3253 => at2
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
| eq3306 => at2
| eq3308 => at2
| eq3309 => at2
| eq3315 => at2
| eq3316 => at2
| eq3319 => at2
| eq3322 => at2
| eq3323 => at2
| eq3326 => at2
| eq3331 => at2
| eq3334 => at2
| eq3342 => at2
| eq3346 => at2
| eq3350 => at2
| eq3353 => at2
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
| eq4283 => at2
| eq4284 => at2
| eq4286 => at2
| eq4287 => at2
| eq4288 => at2
| eq4290 => at2
| eq4291 => at2
| eq4293 => at2
| eq4296 => at2
| eq4297 => at2
| eq4299 => at2
| eq4300 => at2
| eq4301 => at2
| eq4304 => at2
| eq4305 => at2
| eq4314 => at2
| eq4315 => at2
| eq4318 => at2
| eq4320 => at2
| eq4321 => at2
| eq4325 => at2
| eq4327 => at2
| eq4331 => at2
| eq4343 => at2
| eq4358 => at2
| eq4362 => at2
| eq4364 => at2
| eq4369 => at2
| eq4512 => at2


private theorem AT2_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation1 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT2_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  exact hh

private theorem AT2_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3⟩ := h
  exact hh

private theorem AT2_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4⟩ := h
  exact hh

private theorem AT2_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation5 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h5⟩ := h
  exact hh

private theorem AT2_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation8 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h8⟩ := h
  exact hh

private theorem AT2_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation10 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h10⟩ := h
  exact hh

private theorem AT2_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation11 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h11⟩ := h
  exact hh

private theorem AT2_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  exact hh

private theorem AT2_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation16 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h16⟩ := h
  exact hh

private theorem AT2_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation38 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h38⟩ := h
  exact hh

private theorem AT2_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation39 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h39⟩ := h
  exact hh

private theorem AT2_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation40 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h40⟩ := h
  exact hh

private theorem AT2_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation41 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h41⟩ := h
  exact hh

private theorem AT2_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation43 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h43⟩ := h
  exact hh

private theorem AT2_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation47 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h47⟩ := h
  exact hh

private theorem AT2_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation56 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h56⟩ := h
  exact hh

private theorem AT2_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  exact hh

private theorem AT2_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation75 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h75⟩ := h
  exact hh

private theorem AT2_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation307 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h307⟩ := h
  exact hh

private theorem AT2_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation308 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h308⟩ := h
  exact hh

private theorem AT2_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation309 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h309⟩ := h
  exact hh

private theorem AT2_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation310 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h310⟩ := h
  exact hh

private theorem AT2_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation311 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h311⟩ := h
  exact hh

private theorem AT2_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation312 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h312⟩ := h
  exact hh

private theorem AT2_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation313 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h313⟩ := h
  exact hh

private theorem AT2_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation314 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h314⟩ := h
  exact hh

private theorem AT2_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation315 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h315⟩ := h
  exact hh

private theorem AT2_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation316 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h316⟩ := h
  exact hh

private theorem AT2_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation318 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h318⟩ := h
  exact hh

private theorem AT2_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation323 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h323⟩ := h
  exact hh

private theorem AT2_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation325 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h325⟩ := h
  exact hh

private theorem AT2_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation326 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h326⟩ := h
  exact hh

private theorem AT2_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation327 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h327⟩ := h
  exact hh

private theorem AT2_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation329 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h329⟩ := h
  exact hh

private theorem AT2_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation332 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h332⟩ := h
  exact hh

private theorem AT2_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation333 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h333⟩ := h
  exact hh

private theorem AT2_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation343 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h343⟩ := h
  exact hh

private theorem AT2_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation411 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h411⟩ := h
  exact hh

private theorem AT2_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation419 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h419⟩ := h
  exact hh

private theorem AT2_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation429 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h429⟩ := h
  exact hh

private theorem AT2_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation440 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h440⟩ := h
  exact hh

private theorem AT2_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  exact hh

private theorem AT2_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  exact hh

private theorem AT2_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation513 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h513⟩ := h
  exact hh

private theorem AT2_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3253 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT2_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3255 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3255⟩ := h
  exact hh

private theorem AT2_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3256 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3256⟩ := h
  exact hh

private theorem AT2_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3258 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3258⟩ := h
  exact hh

private theorem AT2_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3259 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3259⟩ := h
  exact hh

private theorem AT2_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3260 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3260⟩ := h
  exact hh

private theorem AT2_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3261 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3261⟩ := h
  exact hh

private theorem AT2_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3264 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3264⟩ := h
  exact hh

private theorem AT2_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3265 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3265⟩ := h
  exact hh

private theorem AT2_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3267 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3267⟩ := h
  exact hh

private theorem AT2_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3271 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3271⟩ := h
  exact hh

private theorem AT2_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3273⟩ := h
  exact hh

private theorem AT2_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3274 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3274⟩ := h
  exact hh

private theorem AT2_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3275 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3275⟩ := h
  exact hh

private theorem AT2_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3277⟩ := h
  exact hh

private theorem AT2_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3278 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3278⟩ := h
  exact hh

private theorem AT2_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3290 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3290⟩ := h
  exact hh

private theorem AT2_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3292 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3292⟩ := h
  exact hh

private theorem AT2_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3300 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3300⟩ := h
  exact hh

private theorem AT2_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3306 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3306⟩ := h
  exact hh

private theorem AT2_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3308 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3308⟩ := h
  exact hh

private theorem AT2_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3309 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3309⟩ := h
  exact hh

private theorem AT2_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3315 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3315⟩ := h
  exact hh

private theorem AT2_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3316 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3316⟩ := h
  exact hh

private theorem AT2_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3319 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3319⟩ := h
  exact hh

private theorem AT2_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3322 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3322⟩ := h
  exact hh

private theorem AT2_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3323 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3323⟩ := h
  exact hh

private theorem AT2_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3326 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3326⟩ := h
  exact hh

private theorem AT2_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3331 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3331⟩ := h
  exact hh

private theorem AT2_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3334 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3334⟩ := h
  exact hh

private theorem AT2_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3342 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3342⟩ := h
  exact hh

private theorem AT2_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3346 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3346⟩ := h
  exact hh

private theorem AT2_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3350 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3350⟩ := h
  exact hh

private theorem AT2_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3353 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3353⟩ := h
  exact hh

private theorem AT2_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3388 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3388⟩ := h
  exact hh

private theorem AT2_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation3414 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3414⟩ := h
  exact hh

private theorem AT2_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4268 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4268⟩ := h
  exact hh

private theorem AT2_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4269 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4269⟩ := h
  exact hh

private theorem AT2_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4270 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4270⟩ := h
  exact hh

private theorem AT2_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4271 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4271⟩ := h
  exact hh

private theorem AT2_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4272 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4272⟩ := h
  exact hh

private theorem AT2_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4273⟩ := h
  exact hh

private theorem AT2_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4274 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4274⟩ := h
  exact hh

private theorem AT2_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4275 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4275⟩ := h
  exact hh

private theorem AT2_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4276 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4276⟩ := h
  exact hh

private theorem AT2_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4277⟩ := h
  exact hh

private theorem AT2_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4278 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4278⟩ := h
  exact hh

private theorem AT2_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4279 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4279⟩ := h
  exact hh

private theorem AT2_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4280 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4280⟩ := h
  exact hh

private theorem AT2_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4283 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4283⟩ := h
  exact hh

private theorem AT2_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4284 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4284⟩ := h
  exact hh

private theorem AT2_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4286 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4286⟩ := h
  exact hh

private theorem AT2_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4287 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4287⟩ := h
  exact hh

private theorem AT2_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4288 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4288⟩ := h
  exact hh

private theorem AT2_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4290 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4290⟩ := h
  exact hh

private theorem AT2_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4291 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4291⟩ := h
  exact hh

private theorem AT2_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4293 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4293⟩ := h
  exact hh

private theorem AT2_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4296 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4296⟩ := h
  exact hh

private theorem AT2_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4297 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4297⟩ := h
  exact hh

private theorem AT2_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4299 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4299⟩ := h
  exact hh

private theorem AT2_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4300 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4300⟩ := h
  exact hh

private theorem AT2_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4301 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4301⟩ := h
  exact hh

private theorem AT2_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4304 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4304⟩ := h
  exact hh

private theorem AT2_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4305 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4305⟩ := h
  exact hh

private theorem AT2_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4314 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4314⟩ := h
  exact hh

private theorem AT2_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4315 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4315⟩ := h
  exact hh

private theorem AT2_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4318 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4318⟩ := h
  exact hh

private theorem AT2_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4320 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4320⟩ := h
  exact hh

private theorem AT2_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4321 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4321⟩ := h
  exact hh

private theorem AT2_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4325 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4325⟩ := h
  exact hh

private theorem AT2_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4327 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4327⟩ := h
  exact hh

private theorem AT2_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4331 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4331⟩ := h
  exact hh

private theorem AT2_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4343 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4343⟩ := h
  exact hh

private theorem AT2_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4358 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4358⟩ := h
  exact hh

private theorem AT2_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4362 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4362⟩ := h
  exact hh

private theorem AT2_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4364 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4364⟩ := h
  exact hh

private theorem AT2_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4369 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4369⟩ := h
  exact hh

private theorem AT2_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory2 G) ∧ (Equation4512 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT2_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj2 eqid)) : (AssociativeTheory2 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj2 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at2 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT2_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory2 G) ∧ (EQeq G eqid) <-> (ATearly G (conj2 eqid)) :=
⟨match eqid with
| eq1 => AT2_Equation1_implies G
| eq2 => AT2_Equation2_implies G
| eq3 => AT2_Equation3_implies G
| eq4 => AT2_Equation4_implies G
| eq5 => AT2_Equation5_implies G
| eq8 => AT2_Equation8_implies G
| eq10 => AT2_Equation10_implies G
| eq11 => AT2_Equation11_implies G
| eq14 => AT2_Equation14_implies G
| eq16 => AT2_Equation16_implies G
| eq38 => AT2_Equation38_implies G
| eq39 => AT2_Equation39_implies G
| eq40 => AT2_Equation40_implies G
| eq41 => AT2_Equation41_implies G
| eq43 => AT2_Equation43_implies G
| eq47 => AT2_Equation47_implies G
| eq56 => AT2_Equation56_implies G
| eq66 => AT2_Equation66_implies G
| eq75 => AT2_Equation75_implies G
| eq307 => AT2_Equation307_implies G
| eq308 => AT2_Equation308_implies G
| eq309 => AT2_Equation309_implies G
| eq310 => AT2_Equation310_implies G
| eq311 => AT2_Equation311_implies G
| eq312 => AT2_Equation312_implies G
| eq313 => AT2_Equation313_implies G
| eq314 => AT2_Equation314_implies G
| eq315 => AT2_Equation315_implies G
| eq316 => AT2_Equation316_implies G
| eq318 => AT2_Equation318_implies G
| eq323 => AT2_Equation323_implies G
| eq325 => AT2_Equation325_implies G
| eq326 => AT2_Equation326_implies G
| eq327 => AT2_Equation327_implies G
| eq329 => AT2_Equation329_implies G
| eq332 => AT2_Equation332_implies G
| eq333 => AT2_Equation333_implies G
| eq343 => AT2_Equation343_implies G
| eq411 => AT2_Equation411_implies G
| eq419 => AT2_Equation419_implies G
| eq429 => AT2_Equation429_implies G
| eq440 => AT2_Equation440_implies G
| eq477 => AT2_Equation477_implies G
| eq504 => AT2_Equation504_implies G
| eq513 => AT2_Equation513_implies G
| eq3253 => AT2_Equation3253_implies G
| eq3255 => AT2_Equation3255_implies G
| eq3256 => AT2_Equation3256_implies G
| eq3258 => AT2_Equation3258_implies G
| eq3259 => AT2_Equation3259_implies G
| eq3260 => AT2_Equation3260_implies G
| eq3261 => AT2_Equation3261_implies G
| eq3264 => AT2_Equation3264_implies G
| eq3265 => AT2_Equation3265_implies G
| eq3267 => AT2_Equation3267_implies G
| eq3271 => AT2_Equation3271_implies G
| eq3273 => AT2_Equation3273_implies G
| eq3274 => AT2_Equation3274_implies G
| eq3275 => AT2_Equation3275_implies G
| eq3277 => AT2_Equation3277_implies G
| eq3278 => AT2_Equation3278_implies G
| eq3290 => AT2_Equation3290_implies G
| eq3292 => AT2_Equation3292_implies G
| eq3300 => AT2_Equation3300_implies G
| eq3306 => AT2_Equation3306_implies G
| eq3308 => AT2_Equation3308_implies G
| eq3309 => AT2_Equation3309_implies G
| eq3315 => AT2_Equation3315_implies G
| eq3316 => AT2_Equation3316_implies G
| eq3319 => AT2_Equation3319_implies G
| eq3322 => AT2_Equation3322_implies G
| eq3323 => AT2_Equation3323_implies G
| eq3326 => AT2_Equation3326_implies G
| eq3331 => AT2_Equation3331_implies G
| eq3334 => AT2_Equation3334_implies G
| eq3342 => AT2_Equation3342_implies G
| eq3346 => AT2_Equation3346_implies G
| eq3350 => AT2_Equation3350_implies G
| eq3353 => AT2_Equation3353_implies G
| eq3388 => AT2_Equation3388_implies G
| eq3414 => AT2_Equation3414_implies G
| eq4268 => AT2_Equation4268_implies G
| eq4269 => AT2_Equation4269_implies G
| eq4270 => AT2_Equation4270_implies G
| eq4271 => AT2_Equation4271_implies G
| eq4272 => AT2_Equation4272_implies G
| eq4273 => AT2_Equation4273_implies G
| eq4274 => AT2_Equation4274_implies G
| eq4275 => AT2_Equation4275_implies G
| eq4276 => AT2_Equation4276_implies G
| eq4277 => AT2_Equation4277_implies G
| eq4278 => AT2_Equation4278_implies G
| eq4279 => AT2_Equation4279_implies G
| eq4280 => AT2_Equation4280_implies G
| eq4283 => AT2_Equation4283_implies G
| eq4284 => AT2_Equation4284_implies G
| eq4286 => AT2_Equation4286_implies G
| eq4287 => AT2_Equation4287_implies G
| eq4288 => AT2_Equation4288_implies G
| eq4290 => AT2_Equation4290_implies G
| eq4291 => AT2_Equation4291_implies G
| eq4293 => AT2_Equation4293_implies G
| eq4296 => AT2_Equation4296_implies G
| eq4297 => AT2_Equation4297_implies G
| eq4299 => AT2_Equation4299_implies G
| eq4300 => AT2_Equation4300_implies G
| eq4301 => AT2_Equation4301_implies G
| eq4304 => AT2_Equation4304_implies G
| eq4305 => AT2_Equation4305_implies G
| eq4314 => AT2_Equation4314_implies G
| eq4315 => AT2_Equation4315_implies G
| eq4318 => AT2_Equation4318_implies G
| eq4320 => AT2_Equation4320_implies G
| eq4321 => AT2_Equation4321_implies G
| eq4325 => AT2_Equation4325_implies G
| eq4327 => AT2_Equation4327_implies G
| eq4331 => AT2_Equation4331_implies G
| eq4343 => AT2_Equation4343_implies G
| eq4358 => AT2_Equation4358_implies G
| eq4362 => AT2_Equation4362_implies G
| eq4364 => AT2_Equation4364_implies G
| eq4369 => AT2_Equation4369_implies G
| eq4512 => AT2_Equation4512_implies G
, AT2_conj_implied G eqid⟩

