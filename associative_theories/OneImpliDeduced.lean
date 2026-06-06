import equational_theories.Equations.All
import associative_theories.ConjecturesOneImpli

/- Generated file for the single-equation implication graph -/

open Conjectures


theorem Equation2_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq4276 := Equation66_4512_implies_Equation4276 G eq66 eq4512
  exact Equation4276_4512_implies_Equation1 G eq4276 eq4512

theorem Equation2_4512_implies_Equation3 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  exact Equation10_4512_implies_Equation3 G eq10 eq4512

theorem Equation2_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  exact Equation3_4512_implies_Equation8 G eq3 eq4512

theorem Equation2_4512_implies_Equation10 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation10 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  exact Equation5_4512_implies_Equation10 G eq5 eq4512

theorem Equation2_4512_implies_Equation11 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation11 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  exact Equation14_4512_implies_Equation11 G eq14 eq4512

theorem Equation2_4512_implies_Equation16 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation16 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  exact Equation5_4512_implies_Equation16 G eq5 eq4512

theorem Equation2_4512_implies_Equation38 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation38 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  exact Equation41_4512_implies_Equation38 G eq41 eq4512

theorem Equation2_4512_implies_Equation39 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation39 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  exact Equation5_4512_implies_Equation39 G eq5 eq4512

theorem Equation2_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation40 G eq3350 eq4512

theorem Equation2_4512_implies_Equation43 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation43 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  exact Equation66_4512_implies_Equation43 G eq66 eq4512

theorem Equation2_4512_implies_Equation47 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation47 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq75 := Equation5_4512_implies_Equation75 G eq5 eq4512
  exact Equation75_4512_implies_Equation47 G eq75 eq4512

theorem Equation2_4512_implies_Equation56 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation56 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  exact Equation4_4512_implies_Equation56 G eq4 eq4512

theorem Equation2_4512_implies_Equation75 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation75 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  exact Equation5_4512_implies_Equation75 G eq5 eq4512

theorem Equation2_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation2_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation308 G eq327 eq4512

theorem Equation2_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation309 G eq318 eq4512

theorem Equation2_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation2_4512_implies_Equation311 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation311 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  exact Equation38_4512_implies_Equation311 G eq38 eq4512

theorem Equation2_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation312 G eq343 eq4512

theorem Equation2_4512_implies_Equation313 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation313 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  exact Equation314_4512_implies_Equation313 G eq314 eq4512

theorem Equation2_4512_implies_Equation314 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation314 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  exact Equation41_4512_implies_Equation314 G eq41 eq4512

theorem Equation2_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation2_4512_implies_Equation316 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation316 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  exact Equation3275_4512_implies_Equation316 G eq3275 eq4512

theorem Equation2_4512_implies_Equation318 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation318 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation318 G eq39 eq4512

theorem Equation2_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation323 G eq333 eq4512

theorem Equation2_4512_implies_Equation325 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation325 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation325 G eq332 eq4512

theorem Equation2_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation326 G eq325 eq4512

theorem Equation2_4512_implies_Equation327 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation327 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  exact Equation38_4512_implies_Equation327 G eq38 eq4512

theorem Equation2_4512_implies_Equation329 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation329 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation329 G eq39 eq4512

theorem Equation2_4512_implies_Equation332 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation332 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  exact Equation41_4512_implies_Equation332 G eq41 eq4512

theorem Equation2_4512_implies_Equation333 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation333 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation333 G eq332 eq4512

theorem Equation2_4512_implies_Equation343 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation343 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation343 G eq39 eq4512

theorem Equation2_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  exact Equation440_4512_implies_Equation411 G eq440 eq4512

theorem Equation2_4512_implies_Equation419 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation419 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  exact Equation10_4512_implies_Equation419 G eq10 eq4512

theorem Equation2_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation2_4512_implies_Equation440 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation440 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  exact Equation11_4512_implies_Equation440 G eq11 eq4512

theorem Equation2_4512_implies_Equation477 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation477 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  exact Equation14_4512_implies_Equation477 G eq14 eq4512

theorem Equation2_4512_implies_Equation504 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation504 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  exact Equation477_4512_implies_Equation504 G eq477 eq4512

theorem Equation2_4512_implies_Equation513 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation513 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  exact Equation16_4512_implies_Equation513 G eq16 eq4512

theorem Equation2_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation2_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation2_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation2_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation3258 G eq312 eq4512

theorem Equation2_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3259 G eq3331 eq4512

theorem Equation2_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation2_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation2_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3264 G eq3300 eq4512

theorem Equation2_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3290 := Equation3277_4512_implies_Equation3290 G eq3277 eq4512
  exact Equation3290_4512_implies_Equation3265 G eq3290 eq4512

theorem Equation2_4512_implies_Equation3267 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3267 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3267 G eq3277 eq4512

theorem Equation2_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  exact Equation3388_4512_implies_Equation3271 G eq3388 eq4512

theorem Equation2_4512_implies_Equation3273 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3273 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3273 G eq3277 eq4512

theorem Equation2_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation2_4512_implies_Equation3275 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3275 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3275 G eq3277 eq4512

theorem Equation2_4512_implies_Equation3277 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3277 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  exact Equation314_4512_implies_Equation3277 G eq314 eq4512

theorem Equation2_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation2_4512_implies_Equation3290 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3290 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3290 G eq3277 eq4512

theorem Equation2_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation2_4512_implies_Equation3300 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3300 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation3300 G eq318 eq4512

theorem Equation2_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation2_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation2_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation3309 G eq332 eq4512

theorem Equation2_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation3315 G eq325 eq4512

theorem Equation2_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation3316 G eq333 eq4512

theorem Equation2_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation2_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation2_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation2_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation2_4512_implies_Equation3331 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3331 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  exact Equation38_4512_implies_Equation3331 G eq38 eq4512

theorem Equation2_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation3334 G eq329 eq4512

theorem Equation2_4512_implies_Equation3342 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3342 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation3342 G eq332 eq4512

theorem Equation2_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  exact Equation3342_4512_implies_Equation3346 G eq3342 eq4512

theorem Equation2_4512_implies_Equation3350 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3350 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  exact Equation14_4512_implies_Equation3350 G eq14 eq4512

theorem Equation2_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation3353 G eq333 eq4512

theorem Equation2_4512_implies_Equation3388 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3388 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation3388 G eq39 eq4512

theorem Equation2_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation3414 G eq343 eq4512

theorem Equation2_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4268 G eq4315 eq4512

theorem Equation2_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4269 G eq4287 eq4512

theorem Equation2_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4270 G eq4325 eq4512

theorem Equation2_4512_implies_Equation4271 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4271 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4271 G eq4274 eq4512

theorem Equation2_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation2_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation2_4512_implies_Equation4274 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4274 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  exact Equation314_4512_implies_Equation4274 G eq314 eq4512

theorem Equation2_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4275 G eq4305 eq4512

theorem Equation2_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  exact Equation66_4512_implies_Equation4276 G eq66 eq4512

theorem Equation2_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation2_4512_implies_Equation4278 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4278 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation4278 G eq318 eq4512

theorem Equation2_4512_implies_Equation4279 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4279 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4279 G eq4331 eq4512

theorem Equation2_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4280 G eq4331 eq4512

theorem Equation2_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  exact Equation4364_4512_implies_Equation4283 G eq4364 eq4512

theorem Equation2_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq3309 := Equation332_4512_implies_Equation3309 G eq332 eq4512
  exact Equation3309_4512_implies_Equation4284 G eq3309 eq4512

theorem Equation2_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation2_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation2_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation2_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  exact Equation504_4512_implies_Equation4290 G eq504 eq4512

theorem Equation2_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation4291 G eq333 eq4512

theorem Equation2_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation4293 G eq332 eq4512

theorem Equation2_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation2_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation2_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4299 G eq4274 eq4512

theorem Equation2_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation4300 G eq343 eq4512

theorem Equation2_4512_implies_Equation4301 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4301 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4301 G eq4274 eq4512

theorem Equation2_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation2_4512_implies_Equation4305 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4305 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation4305 G eq3350 eq4512

theorem Equation2_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation4314 G eq325 eq4512

theorem Equation2_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation4315 G eq327 eq4512

theorem Equation2_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4318 G eq4331 eq4512

theorem Equation2_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  exact Equation4364_4512_implies_Equation4320 G eq4364 eq4512

theorem Equation2_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation4321 G eq332 eq4512

theorem Equation2_4512_implies_Equation4325 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4325 G := by
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation4325 G eq3350 eq4512

theorem Equation2_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4327 G eq4331 eq4512

theorem Equation2_4512_implies_Equation4331 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4331 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4331 G eq4274 eq4512

theorem Equation2_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation4343 G eq332 eq4512

theorem Equation2_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4358 G eq43 eq4512

theorem Equation2_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4362 G eq43 eq4512

theorem Equation2_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation2_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq2 : Equation2 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation3_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  exact Equation47_4512_implies_Equation1 G eq47 eq4512

theorem Equation3_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq323 := Equation3309_4512_implies_Equation323 G eq3309 eq4512
  exact Equation323_4512_implies_Equation307 G eq323 eq4512

theorem Equation3_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation323 G eq3309 eq4512

theorem Equation3_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation326 G eq3309 eq4512

theorem Equation3_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  exact Equation8_4512_implies_Equation411 G eq8 eq4512

theorem Equation3_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  exact Equation8_4512_implies_Equation3306 G eq8 eq4512

theorem Equation3_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation3316 G eq3309 eq4512

theorem Equation3_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  exact Equation8_4512_implies_Equation3319 G eq8 eq4512

theorem Equation3_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3 : Equation3 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation4284 G eq3309 eq4512

theorem Equation4_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq56 := Equation4_4512_implies_Equation56 G eq4 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact Equation47_4512_implies_Equation1 G eq47 eq4512

theorem Equation4_4512_implies_Equation3 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  exact Equation10_4512_implies_Equation3 G eq10 eq4512

theorem Equation4_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  exact Equation3_4512_implies_Equation8 G eq3 eq4512

theorem Equation4_4512_implies_Equation47 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation47 G := by
  have eq56 := Equation4_4512_implies_Equation56 G eq4 eq4512
  exact Equation56_4512_implies_Equation47 G eq56 eq4512

theorem Equation4_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3309_4512_implies_Equation3316 G eq3309 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation4_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation308 G eq327 eq4512

theorem Equation4_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation309 G eq329 eq4512

theorem Equation4_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  exact Equation3260_4512_implies_Equation310 G eq3260 eq4512

theorem Equation4_4512_implies_Equation311 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation311 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  exact Equation38_4512_implies_Equation311 G eq38 eq4512

theorem Equation4_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation323 G eq3309 eq4512

theorem Equation4_4512_implies_Equation325 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation325 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation325 G eq327 eq4512

theorem Equation4_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation326 G eq3309 eq4512

theorem Equation4_4512_implies_Equation327 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation327 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  exact Equation38_4512_implies_Equation327 G eq38 eq4512

theorem Equation4_4512_implies_Equation329 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation329 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  exact Equation38_4512_implies_Equation329 G eq38 eq4512

theorem Equation4_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  exact Equation440_4512_implies_Equation411 G eq440 eq4512

theorem Equation4_4512_implies_Equation419 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation419 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  exact Equation10_4512_implies_Equation419 G eq10 eq4512

theorem Equation4_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation4_4512_implies_Equation440 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation440 G := by
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  exact Equation11_4512_implies_Equation440 G eq11 eq4512

theorem Equation4_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation4_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation4_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation4_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3258 G eq3326 eq4512

theorem Equation4_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3259 G eq3331 eq4512

theorem Equation4_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation4_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation4_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3264 G eq3267 eq4512

theorem Equation4_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3265 G eq3267 eq4512

theorem Equation4_4512_implies_Equation3267 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3267 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  exact Equation311_4512_implies_Equation3267 G eq311 eq4512

theorem Equation4_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation4_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation4_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3309 G eq329 eq4512

theorem Equation4_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation4_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3316 G eq3326 eq4512

theorem Equation4_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation4_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation4_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation4_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation4_4512_implies_Equation3331 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3331 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  exact Equation38_4512_implies_Equation3331 G eq38 eq4512

theorem Equation4_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  exact Equation419_4512_implies_Equation3334 G eq419 eq4512

theorem Equation4_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4268 G eq4315 eq4512

theorem Equation4_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4269 G eq4287 eq4512

theorem Equation4_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation4_4512_implies_Equation4271 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4271 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  exact Equation311_4512_implies_Equation4271 G eq311 eq4512

theorem Equation4_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation4_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation4_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation4_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation4_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation4_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4314 G eq4315 eq4512

theorem Equation4_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation4315 G eq327 eq4512

theorem Equation4_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4318 G eq4271 eq4512

theorem Equation4_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq4 : Equation4 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation4358 G eq3331 eq4512

theorem Equation5_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq75 := Equation5_4512_implies_Equation75 G eq5 eq4512
  have eq47 := Equation75_4512_implies_Equation47 G eq75 eq4512
  exact Equation47_4512_implies_Equation1 G eq47 eq4512

theorem Equation5_4512_implies_Equation3 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  exact Equation10_4512_implies_Equation3 G eq10 eq4512

theorem Equation5_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  exact Equation3_4512_implies_Equation8 G eq3 eq4512

theorem Equation5_4512_implies_Equation47 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation47 G := by
  have eq75 := Equation5_4512_implies_Equation75 G eq5 eq4512
  exact Equation75_4512_implies_Equation47 G eq75 eq4512

theorem Equation5_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3309_4512_implies_Equation3316 G eq3309 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation5_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation309 G eq329 eq4512

theorem Equation5_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation312 G eq343 eq4512

theorem Equation5_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation5_4512_implies_Equation318 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation318 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation318 G eq39 eq4512

theorem Equation5_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation323 G eq3309 eq4512

theorem Equation5_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation326 G eq3309 eq4512

theorem Equation5_4512_implies_Equation329 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation329 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation329 G eq39 eq4512

theorem Equation5_4512_implies_Equation333 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation333 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation333 G eq343 eq4512

theorem Equation5_4512_implies_Equation343 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation343 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation343 G eq39 eq4512

theorem Equation5_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq513 := Equation16_4512_implies_Equation513 G eq16 eq4512
  exact Equation513_4512_implies_Equation411 G eq513 eq4512

theorem Equation5_4512_implies_Equation419 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation419 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  exact Equation10_4512_implies_Equation419 G eq10 eq4512

theorem Equation5_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation5_4512_implies_Equation513 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation513 G := by
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  exact Equation16_4512_implies_Equation513 G eq16 eq4512

theorem Equation5_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation5_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation3255 G eq3322 eq4512

theorem Equation5_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation3258 G eq312 eq4512

theorem Equation5_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation5_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3264 G eq3300 eq4512

theorem Equation5_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation3271 G eq3388 eq4512

theorem Equation5_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation5_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation5_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation5_4512_implies_Equation3300 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3300 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation3300 G eq318 eq4512

theorem Equation5_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation5_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3309 G eq329 eq4512

theorem Equation5_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation3316 G eq333 eq4512

theorem Equation5_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation5_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation5_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation5_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  exact Equation419_4512_implies_Equation3334 G eq419 eq4512

theorem Equation5_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation3346 G eq3388 eq4512

theorem Equation5_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3346 := Equation3388_4512_implies_Equation3346 G eq3388 eq4512
  exact Equation3346_4512_implies_Equation3353 G eq3346 eq4512

theorem Equation5_4512_implies_Equation3388 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3388 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  exact Equation39_4512_implies_Equation3388 G eq39 eq4512

theorem Equation5_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation3414 G eq343 eq4512

theorem Equation5_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4269 G eq4287 eq4512

theorem Equation5_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation5_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation5_4512_implies_Equation4278 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4278 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation4278 G eq318 eq4512

theorem Equation5_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation5_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation5_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation4291 G eq333 eq4512

theorem Equation5_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation5_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation4300 G eq343 eq4512

theorem Equation5_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation5_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq4362 := Equation3388_4512_implies_Equation4362 G eq3388 eq4512
  exact Equation4362_4512_implies_Equation4320 G eq4362 eq4512

theorem Equation5_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4327 G eq4278 eq4512

theorem Equation5_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq5 : Equation5 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation4362 G eq3388 eq4512

theorem Equation8_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq8 : Equation8 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation8_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq8 : Equation8 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation10_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  exact Equation47_4512_implies_Equation1 G eq47 eq4512

theorem Equation10_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  exact Equation3_4512_implies_Equation8 G eq3 eq4512

theorem Equation10_4512_implies_Equation47 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation47 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  exact Equation3_4512_implies_Equation47 G eq3 eq4512

theorem Equation10_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  have eq3258 := Equation3326_4512_implies_Equation3258 G eq3326 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation10_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation309 G eq329 eq4512

theorem Equation10_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation323 G eq3309 eq4512

theorem Equation10_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation326 G eq3309 eq4512

theorem Equation10_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  exact Equation8_4512_implies_Equation411 G eq8 eq4512

theorem Equation10_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation10_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation10_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation3255 G eq3322 eq4512

theorem Equation10_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3258 G eq3326 eq4512

theorem Equation10_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation10_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation3264 G eq309 eq4512

theorem Equation10_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  exact Equation8_4512_implies_Equation3306 G eq8 eq4512

theorem Equation10_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation3309 G eq329 eq4512

theorem Equation10_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation3316 G eq3309 eq4512

theorem Equation10_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  exact Equation8_4512_implies_Equation3319 G eq8 eq4512

theorem Equation10_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation10_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation10_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation3334 G eq329 eq4512

theorem Equation10_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation10_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  exact Equation3309_4512_implies_Equation4284 G eq3309 eq4512

theorem Equation10_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq10 : Equation10 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation11_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation11_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq419 := Equation11_4512_implies_Equation419 G eq11 eq4512
  have eq429 := Equation419_4512_implies_Equation429 G eq419 eq4512
  exact Equation429_4512_implies_Equation8 G eq429 eq4512

theorem Equation11_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  exact Equation440_4512_implies_Equation411 G eq440 eq4512

theorem Equation11_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq419 := Equation11_4512_implies_Equation419 G eq11 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation11_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation11_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3323 := Equation3331_4512_implies_Equation3323 G eq3331 eq4512
  exact Equation3323_4512_implies_Equation3256 G eq3323 eq4512

theorem Equation11_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3259 G eq3331 eq4512

theorem Equation11_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation11_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation11_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation11_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation11_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation11_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation11_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3334 G eq3331 eq4512

theorem Equation11_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation11_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation11_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq11 : Equation11 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation4358 G eq3331 eq4512

theorem Equation14_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation14_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq419 := Equation11_4512_implies_Equation419 G eq11 eq4512
  have eq429 := Equation419_4512_implies_Equation429 G eq419 eq4512
  exact Equation429_4512_implies_Equation8 G eq429 eq4512

theorem Equation14_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation40 G eq3350 eq4512

theorem Equation14_4512_implies_Equation43 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation43 G := by
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  exact Equation477_4512_implies_Equation43 G eq477 eq4512

theorem Equation14_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  exact Equation440_4512_implies_Equation411 G eq440 eq4512

theorem Equation14_4512_implies_Equation419 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation419 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  exact Equation11_4512_implies_Equation419 G eq11 eq4512

theorem Equation14_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq419 := Equation11_4512_implies_Equation419 G eq11 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation14_4512_implies_Equation440 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation440 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  exact Equation11_4512_implies_Equation440 G eq11 eq4512

theorem Equation14_4512_implies_Equation504 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation504 G := by
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  exact Equation477_4512_implies_Equation504 G eq477 eq4512

theorem Equation14_4512_implies_Equation513 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation513 G := by
  have eq16 := Equation14_4512_implies_Equation16 G eq14 eq4512
  exact Equation16_4512_implies_Equation513 G eq16 eq4512

theorem Equation14_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation14_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation14_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation14_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation14_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation3271 G eq40 eq4512

theorem Equation14_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq16 := Equation14_4512_implies_Equation16 G eq14 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation14_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation14_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation14_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation14_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation14_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation14_4512_implies_Equation3331 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3331 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  exact Equation11_4512_implies_Equation3331 G eq11 eq4512

theorem Equation14_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation3334 G eq3331 eq4512

theorem Equation14_4512_implies_Equation3342 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3342 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation3342 G eq3350 eq4512

theorem Equation14_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  exact Equation3342_4512_implies_Equation3346 G eq3342 eq4512

theorem Equation14_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq16 := Equation14_4512_implies_Equation16 G eq14 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3346 := Equation3388_4512_implies_Equation3346 G eq3388 eq4512
  exact Equation3346_4512_implies_Equation3353 G eq3346 eq4512

theorem Equation14_4512_implies_Equation3388 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3388 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation3388 G eq3350 eq4512

theorem Equation14_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq3388 := Equation3350_4512_implies_Equation3388 G eq3350 eq4512
  exact Equation3388_4512_implies_Equation3414 G eq3388 eq4512

theorem Equation14_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4270 G eq4325 eq4512

theorem Equation14_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation14_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4275 G eq4305 eq4512

theorem Equation14_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4283 G eq4305 eq4512

theorem Equation14_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  exact Equation504_4512_implies_Equation4290 G eq504 eq4512

theorem Equation14_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation14_4512_implies_Equation4305 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4305 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation4305 G eq3350 eq4512

theorem Equation14_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4320 G eq4325 eq4512

theorem Equation14_4512_implies_Equation4325 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4325 G := by
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  exact Equation3350_4512_implies_Equation4325 G eq3350 eq4512

theorem Equation14_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  exact Equation3331_4512_implies_Equation4358 G eq3331 eq4512

theorem Equation14_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4362 G eq43 eq4512

theorem Equation14_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation14_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq14 : Equation14 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation16_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq513 := Equation16_4512_implies_Equation513 G eq16 eq4512
  have eq411 := Equation513_4512_implies_Equation411 G eq513 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation16_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  have eq429 := Equation419_4512_implies_Equation429 G eq419 eq4512
  exact Equation429_4512_implies_Equation8 G eq429 eq4512

theorem Equation16_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq513 := Equation16_4512_implies_Equation513 G eq16 eq4512
  exact Equation513_4512_implies_Equation411 G eq513 eq4512

theorem Equation16_4512_implies_Equation429 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation429 G := by
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  exact Equation419_4512_implies_Equation429 G eq419 eq4512

theorem Equation16_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation16_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation16_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  exact Equation3388_4512_implies_Equation3271 G eq3388 eq4512

theorem Equation16_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation16_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation16_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation16_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  exact Equation419_4512_implies_Equation3334 G eq419 eq4512

theorem Equation16_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  exact Equation3388_4512_implies_Equation3346 G eq3388 eq4512

theorem Equation16_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3346 := Equation3388_4512_implies_Equation3346 G eq3388 eq4512
  exact Equation3346_4512_implies_Equation3353 G eq3346 eq4512

theorem Equation16_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  exact Equation3388_4512_implies_Equation3414 G eq3388 eq4512

theorem Equation16_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation16_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq4362 := Equation3388_4512_implies_Equation4362 G eq3388 eq4512
  exact Equation4362_4512_implies_Equation4320 G eq4362 eq4512

theorem Equation16_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq16 : Equation16 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  exact Equation3388_4512_implies_Equation4362 G eq3388 eq4512

theorem Equation38_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation38_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  have eq3258 := Equation3326_4512_implies_Equation3258 G eq3326 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation38_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation308 G eq327 eq4512

theorem Equation38_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation309 G eq329 eq4512

theorem Equation38_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  exact Equation3260_4512_implies_Equation310 G eq3260 eq4512

theorem Equation38_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation323 G eq3326 eq4512

theorem Equation38_4512_implies_Equation325 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation325 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation325 G eq327 eq4512

theorem Equation38_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation326 G eq3322 eq4512

theorem Equation38_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation38_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation38_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation38_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3258 G eq3326 eq4512

theorem Equation38_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3259 G eq3331 eq4512

theorem Equation38_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation38_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation38_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation3264 G eq309 eq4512

theorem Equation38_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3265 G eq3267 eq4512

theorem Equation38_4512_implies_Equation3267 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3267 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  exact Equation311_4512_implies_Equation3267 G eq311 eq4512

theorem Equation38_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation38_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation38_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3309 G eq329 eq4512

theorem Equation38_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation38_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq325 := Equation327_4512_implies_Equation325 G eq327 eq4512
  exact Equation325_4512_implies_Equation3316 G eq325 eq4512

theorem Equation38_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation38_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation38_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation38_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation38_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation3334 G eq329 eq4512

theorem Equation38_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4268 G eq4315 eq4512

theorem Equation38_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation38_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation38_4512_implies_Equation4271 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4271 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  exact Equation311_4512_implies_Equation4271 G eq311 eq4512

theorem Equation38_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation38_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation38_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation38_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation38_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation38_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4314 G eq4315 eq4512

theorem Equation38_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation4315 G eq327 eq4512

theorem Equation38_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4318 G eq4271 eq4512

theorem Equation38_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq38 : Equation38 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation4358 G eq3331 eq4512

theorem Equation39_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation39_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation39_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation309 G eq318 eq4512

theorem Equation39_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation312 G eq343 eq4512

theorem Equation39_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation39_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation323 G eq333 eq4512

theorem Equation39_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation326 G eq3322 eq4512

theorem Equation39_4512_implies_Equation333 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation333 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation333 G eq343 eq4512

theorem Equation39_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation39_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation3255 G eq3322 eq4512

theorem Equation39_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3258 G eq3326 eq4512

theorem Equation39_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation39_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation3264 G eq309 eq4512

theorem Equation39_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation3271 G eq3388 eq4512

theorem Equation39_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation39_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation39_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation39_4512_implies_Equation3300 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3300 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation3300 G eq318 eq4512

theorem Equation39_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation39_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3309 G eq329 eq4512

theorem Equation39_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3309 := Equation329_4512_implies_Equation3309 G eq329 eq4512
  exact Equation3309_4512_implies_Equation3316 G eq3309 eq4512

theorem Equation39_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation39_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation39_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation39_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3334 G eq329 eq4512

theorem Equation39_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation3346 G eq3388 eq4512

theorem Equation39_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation3353 G eq333 eq4512

theorem Equation39_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation3414 G eq343 eq4512

theorem Equation39_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation39_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq4300 := Equation343_4512_implies_Equation4300 G eq343 eq4512
  exact Equation4300_4512_implies_Equation4272 G eq4300 eq4512

theorem Equation39_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation39_4512_implies_Equation4278 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4278 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation4278 G eq318 eq4512

theorem Equation39_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation39_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation39_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation4291 G eq333 eq4512

theorem Equation39_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation39_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation4300 G eq343 eq4512

theorem Equation39_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation39_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  have eq4362 := Equation3388_4512_implies_Equation4362 G eq3388 eq4512
  exact Equation4362_4512_implies_Equation4320 G eq4362 eq4512

theorem Equation39_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4327 G eq4278 eq4512

theorem Equation39_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq39 : Equation39 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation4362 G eq3388 eq4512

theorem Equation40_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation40_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation40_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation40_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation3261 G eq3271 eq4512

theorem Equation40_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation40_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation40_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation40_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq40 : Equation40 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation41_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq4293 := Equation332_4512_implies_Equation4293 G eq332 eq4512
  exact Equation4293_4512_implies_Equation1 G eq4293 eq4512

theorem Equation41_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  exact Equation3350_4512_implies_Equation40 G eq3350 eq4512

theorem Equation41_4512_implies_Equation43 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation43 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  exact Equation3342_4512_implies_Equation43 G eq3342 eq4512

theorem Equation41_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation41_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation308 G eq327 eq4512

theorem Equation41_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation309 G eq318 eq4512

theorem Equation41_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation41_4512_implies_Equation311 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation311 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  exact Equation38_4512_implies_Equation311 G eq38 eq4512

theorem Equation41_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation312 G eq343 eq4512

theorem Equation41_4512_implies_Equation313 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation313 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  exact Equation314_4512_implies_Equation313 G eq314 eq4512

theorem Equation41_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation41_4512_implies_Equation316 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation316 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  exact Equation3275_4512_implies_Equation316 G eq3275 eq4512

theorem Equation41_4512_implies_Equation318 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation318 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  exact Equation39_4512_implies_Equation318 G eq39 eq4512

theorem Equation41_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation323 G eq333 eq4512

theorem Equation41_4512_implies_Equation325 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation325 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation325 G eq332 eq4512

theorem Equation41_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation326 G eq325 eq4512

theorem Equation41_4512_implies_Equation327 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation327 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  exact Equation38_4512_implies_Equation327 G eq38 eq4512

theorem Equation41_4512_implies_Equation329 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation329 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  exact Equation39_4512_implies_Equation329 G eq39 eq4512

theorem Equation41_4512_implies_Equation333 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation333 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation333 G eq332 eq4512

theorem Equation41_4512_implies_Equation343 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation343 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  exact Equation39_4512_implies_Equation343 G eq39 eq4512

theorem Equation41_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation41_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation41_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation41_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3258 G eq3326 eq4512

theorem Equation41_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation41_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation41_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation41_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation3264 G eq309 eq4512

theorem Equation41_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3290 := Equation3277_4512_implies_Equation3290 G eq3277 eq4512
  exact Equation3290_4512_implies_Equation3265 G eq3290 eq4512

theorem Equation41_4512_implies_Equation3267 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3267 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3267 G eq3277 eq4512

theorem Equation41_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation3271 G eq40 eq4512

theorem Equation41_4512_implies_Equation3273 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3273 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3273 G eq3277 eq4512

theorem Equation41_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation41_4512_implies_Equation3275 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3275 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3275 G eq3277 eq4512

theorem Equation41_4512_implies_Equation3277 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3277 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  exact Equation314_4512_implies_Equation3277 G eq314 eq4512

theorem Equation41_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation41_4512_implies_Equation3290 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3290 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3290 G eq3277 eq4512

theorem Equation41_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation41_4512_implies_Equation3300 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3300 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation3300 G eq318 eq4512

theorem Equation41_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation41_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation41_4512_implies_Equation3309 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3309 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation3309 G eq332 eq4512

theorem Equation41_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation3315 G eq325 eq4512

theorem Equation41_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation3316 G eq325 eq4512

theorem Equation41_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation41_4512_implies_Equation3322 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3322 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3322 G eq329 eq4512

theorem Equation41_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation41_4512_implies_Equation3326 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3326 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3326 G eq329 eq4512

theorem Equation41_4512_implies_Equation3331 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3331 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  exact Equation38_4512_implies_Equation3331 G eq38 eq4512

theorem Equation41_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation3334 G eq329 eq4512

theorem Equation41_4512_implies_Equation3342 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3342 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation3342 G eq332 eq4512

theorem Equation41_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  exact Equation3342_4512_implies_Equation3346 G eq3342 eq4512

theorem Equation41_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation3353 G eq333 eq4512

theorem Equation41_4512_implies_Equation3388 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3388 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  exact Equation39_4512_implies_Equation3388 G eq39 eq4512

theorem Equation41_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation3414 G eq343 eq4512

theorem Equation41_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4268 G eq4315 eq4512

theorem Equation41_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4269 G eq4287 eq4512

theorem Equation41_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4270 G eq4325 eq4512

theorem Equation41_4512_implies_Equation4271 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4271 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4271 G eq4274 eq4512

theorem Equation41_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation41_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation41_4512_implies_Equation4274 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4274 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  exact Equation314_4512_implies_Equation4274 G eq314 eq4512

theorem Equation41_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4275 G eq4305 eq4512

theorem Equation41_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation41_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation41_4512_implies_Equation4278 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4278 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  exact Equation318_4512_implies_Equation4278 G eq318 eq4512

theorem Equation41_4512_implies_Equation4279 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4279 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4279 G eq4331 eq4512

theorem Equation41_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4280 G eq4331 eq4512

theorem Equation41_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4283 G eq4305 eq4512

theorem Equation41_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq3309 := Equation332_4512_implies_Equation3309 G eq332 eq4512
  exact Equation3309_4512_implies_Equation4284 G eq3309 eq4512

theorem Equation41_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation41_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  exact Equation329_4512_implies_Equation4287 G eq329 eq4512

theorem Equation41_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation41_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation41_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation4291 G eq333 eq4512

theorem Equation41_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation4293 G eq332 eq4512

theorem Equation41_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation41_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation41_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4299 G eq4274 eq4512

theorem Equation41_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  exact Equation343_4512_implies_Equation4300 G eq343 eq4512

theorem Equation41_4512_implies_Equation4301 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4301 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4301 G eq4274 eq4512

theorem Equation41_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation41_4512_implies_Equation4305 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4305 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  exact Equation3350_4512_implies_Equation4305 G eq3350 eq4512

theorem Equation41_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation4314 G eq325 eq4512

theorem Equation41_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  exact Equation327_4512_implies_Equation4315 G eq327 eq4512

theorem Equation41_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4318 G eq4331 eq4512

theorem Equation41_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4320 G eq4325 eq4512

theorem Equation41_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation4321 G eq332 eq4512

theorem Equation41_4512_implies_Equation4325 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4325 G := by
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  exact Equation3350_4512_implies_Equation4325 G eq3350 eq4512

theorem Equation41_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4327 G eq4331 eq4512

theorem Equation41_4512_implies_Equation4331 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4331 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4331 G eq4274 eq4512

theorem Equation41_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  exact Equation332_4512_implies_Equation4343 G eq332 eq4512

theorem Equation41_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq38 := Equation41_4512_implies_Equation38 G eq41 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  exact Equation3331_4512_implies_Equation4358 G eq3331 eq4512

theorem Equation41_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq39 := Equation41_4512_implies_Equation39 G eq41 eq4512
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  exact Equation3388_4512_implies_Equation4362 G eq3388 eq4512

theorem Equation41_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4364 G eq4274 eq4512

theorem Equation41_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq41 : Equation41 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4369 G eq4274 eq4512

theorem Equation43_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq43 : Equation43 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation43_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq43 : Equation43 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  exact Equation4364_4512_implies_Equation4283 G eq4364 eq4512

theorem Equation43_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq43 : Equation43 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact Equation4369_4512_implies_Equation4290 G eq4369 eq4512

theorem Equation43_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq43 : Equation43 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  exact Equation4364_4512_implies_Equation4320 G eq4364 eq4512

theorem Equation56_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq56 : Equation56 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact Equation47_4512_implies_Equation1 G eq47 eq4512

theorem Equation66_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4276 := Equation66_4512_implies_Equation4276 G eq66 eq4512
  exact Equation4276_4512_implies_Equation1 G eq4276 eq4512

theorem Equation66_4512_implies_Equation47 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation47 G := by
  have eq75 := Equation66_4512_implies_Equation75 G eq66 eq4512
  exact Equation75_4512_implies_Equation47 G eq75 eq4512

theorem Equation66_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation66_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  exact Equation4364_4512_implies_Equation4290 G eq4364 eq4512

theorem Equation66_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  exact Equation4362_4512_implies_Equation4320 G eq4362 eq4512

theorem Equation66_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4358 G eq43 eq4512

theorem Equation66_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4362 G eq43 eq4512

theorem Equation66_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation66_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq66 : Equation66 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq43 := Equation66_4512_implies_Equation43 G eq66 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation75_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq75 : Equation75 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq47 := Equation75_4512_implies_Equation47 G eq75 eq4512
  exact Equation47_4512_implies_Equation1 G eq47 eq4512

theorem Equation307_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq307 : Equation307 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation308_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq308 : Equation308 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation308_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq308 : Equation308 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation308_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq308 : Equation308 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation309_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation309_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation309_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation309_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation309_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation309_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation309_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq309 : Equation309 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation310_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  have eq4268 := Equation4288_4512_implies_Equation4268 G eq4288 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation310_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3258 := Equation310_4512_implies_Equation3258 G eq310 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation310_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation310_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation310_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation310_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3261 G eq3259 eq4512

theorem Equation310_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation310_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation310_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq310 : Equation310 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4284 G eq4288 eq4512

theorem Equation311_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation311_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation311_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation311_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  exact Equation3265_4512_implies_Equation310 G eq3265 eq4512

theorem Equation311_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation311_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation311_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation311_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation311_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation311_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation311_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation311_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3264 G eq3267 eq4512

theorem Equation311_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  exact Equation3267_4512_implies_Equation3265 G eq3267 eq4512

theorem Equation311_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4288 := Equation4271_4512_implies_Equation4288 G eq4271 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation311_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation311_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4288 := Equation4271_4512_implies_Equation4288 G eq4271 eq4512
  exact Equation4288_4512_implies_Equation4270 G eq4288 eq4512

theorem Equation311_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4358 := Equation4271_4512_implies_Equation4358 G eq4271 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation311_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4288 := Equation4271_4512_implies_Equation4288 G eq4271 eq4512
  exact Equation4288_4512_implies_Equation4284 G eq4288 eq4512

theorem Equation311_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation311_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4287 G eq4271 eq4512

theorem Equation311_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation311_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4315 := Equation4271_4512_implies_Equation4315 G eq4271 eq4512
  exact Equation4315_4512_implies_Equation4314 G eq4315 eq4512

theorem Equation311_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4315 G eq4271 eq4512

theorem Equation311_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4318 G eq4271 eq4512

theorem Equation311_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq311 : Equation311 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  exact Equation4271_4512_implies_Equation4358 G eq4271 eq4512

theorem Equation312_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq312 : Equation312 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  exact Equation4272_4512_implies_Equation1 G eq4272 eq4512

theorem Equation312_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq312 : Equation312 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation312_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq312 : Equation312 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation313_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq309 := Equation313_4512_implies_Equation309 G eq313 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation313_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation40 G eq316 eq4512

theorem Equation313_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq309 := Equation313_4512_implies_Equation309 G eq313 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation313_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation313_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation313_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation313_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation313_4512_implies_Equation316 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation316 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  exact Equation3275_4512_implies_Equation316 G eq3275 eq4512

theorem Equation313_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq309 := Equation313_4512_implies_Equation309 G eq313 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation313_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation313_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation313_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation313_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation313_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  exact Equation3273_4512_implies_Equation3260 G eq3273 eq4512

theorem Equation313_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation313_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  exact Equation3275_4512_implies_Equation3264 G eq3275 eq4512

theorem Equation313_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq3290 := Equation313_4512_implies_Equation3290 G eq313 eq4512
  exact Equation3290_4512_implies_Equation3265 G eq3290 eq4512

theorem Equation313_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation313_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq3290 := Equation313_4512_implies_Equation3290 G eq313 eq4512
  exact Equation3290_4512_implies_Equation3274 G eq3290 eq4512

theorem Equation313_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation313_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  exact Equation3273_4512_implies_Equation3292 G eq3273 eq4512

theorem Equation313_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  exact Equation4286_4512_implies_Equation4268 G eq4286 eq4512

theorem Equation313_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq309 := Equation313_4512_implies_Equation309 G eq313 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation313_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4325 := Equation4331_4512_implies_Equation4325 G eq4331 eq4512
  exact Equation4325_4512_implies_Equation4270 G eq4325 eq4512

theorem Equation313_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4327 := Equation4331_4512_implies_Equation4327 G eq4331 eq4512
  exact Equation4327_4512_implies_Equation4272 G eq4327 eq4512

theorem Equation313_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4305 := Equation4301_4512_implies_Equation4305 G eq4301 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation313_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  exact Equation4296_4512_implies_Equation4275 G eq4296 eq4512

theorem Equation313_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation313_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  exact Equation4301_4512_implies_Equation4277 G eq4301 eq4512

theorem Equation313_4512_implies_Equation4279 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4279 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact Equation4331_4512_implies_Equation4279 G eq4331 eq4512

theorem Equation313_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact Equation4331_4512_implies_Equation4280 G eq4331 eq4512

theorem Equation313_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  exact Equation4286_4512_implies_Equation4283 G eq4286 eq4512

theorem Equation313_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation313_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  exact Equation4301_4512_implies_Equation4286 G eq4301 eq4512

theorem Equation313_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4288 G eq4299 eq4512

theorem Equation313_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation313_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  exact Equation4296_4512_implies_Equation4291 G eq4296 eq4512

theorem Equation313_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4277 := Equation4301_4512_implies_Equation4277 G eq4301 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation313_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  exact Equation4301_4512_implies_Equation4296 G eq4301 eq4512

theorem Equation313_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation313_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation4299 G eq316 eq4512

theorem Equation313_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation313_4512_implies_Equation4305 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4305 G := by
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  exact Equation4301_4512_implies_Equation4305 G eq4301 eq4512

theorem Equation313_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4314 G eq4318 eq4512

theorem Equation313_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact Equation4331_4512_implies_Equation4318 G eq4331 eq4512

theorem Equation313_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4327 := Equation4331_4512_implies_Equation4327 G eq4331 eq4512
  exact Equation4327_4512_implies_Equation4320 G eq4327 eq4512

theorem Equation313_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4279 := Equation4331_4512_implies_Equation4279 G eq4331 eq4512
  exact Equation4279_4512_implies_Equation4321 G eq4279 eq4512

theorem Equation313_4512_implies_Equation4325 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4325 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact Equation4331_4512_implies_Equation4325 G eq4331 eq4512

theorem Equation313_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact Equation4331_4512_implies_Equation4327 G eq4331 eq4512

theorem Equation313_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq313 : Equation313 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation314_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation314_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  exact Equation316_4512_implies_Equation40 G eq316 eq4512

theorem Equation314_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation314_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation314_4512_implies_Equation309 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation309 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  exact Equation318_4512_implies_Equation309 G eq318 eq4512

theorem Equation314_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation314_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation314_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation314_4512_implies_Equation316 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation316 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  exact Equation3275_4512_implies_Equation316 G eq3275 eq4512

theorem Equation314_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation314_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation314_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation314_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation314_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation314_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation314_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation314_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3264 G eq3300 eq4512

theorem Equation314_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3290 := Equation3277_4512_implies_Equation3290 G eq3277 eq4512
  exact Equation3290_4512_implies_Equation3265 G eq3290 eq4512

theorem Equation314_4512_implies_Equation3267 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3267 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3267 G eq3277 eq4512

theorem Equation314_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation314_4512_implies_Equation3273 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3273 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3273 G eq3277 eq4512

theorem Equation314_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation314_4512_implies_Equation3275 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3275 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3275 G eq3277 eq4512

theorem Equation314_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation314_4512_implies_Equation3290 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3290 G := by
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  exact Equation3277_4512_implies_Equation3290 G eq3277 eq4512

theorem Equation314_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation314_4512_implies_Equation3300 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation3300 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  exact Equation318_4512_implies_Equation3300 G eq318 eq4512

theorem Equation314_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4286 := Equation4271_4512_implies_Equation4286 G eq4271 eq4512
  exact Equation4286_4512_implies_Equation4268 G eq4286 eq4512

theorem Equation314_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq311 := Equation314_4512_implies_Equation311 G eq314 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation314_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4270 G eq4318 eq4512

theorem Equation314_4512_implies_Equation4271 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4271 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4271 G eq4274 eq4512

theorem Equation314_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4327 := Equation4331_4512_implies_Equation4327 G eq4331 eq4512
  exact Equation4327_4512_implies_Equation4272 G eq4327 eq4512

theorem Equation314_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4301 := Equation4274_4512_implies_Equation4301 G eq4274 eq4512
  have eq4305 := Equation4301_4512_implies_Equation4305 G eq4301 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation314_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4275 G eq4296 eq4512

theorem Equation314_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation314_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation314_4512_implies_Equation4278 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4278 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  exact Equation318_4512_implies_Equation4278 G eq318 eq4512

theorem Equation314_4512_implies_Equation4279 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4279 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4279 G eq4331 eq4512

theorem Equation314_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4280 G eq4331 eq4512

theorem Equation314_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4364 := Equation4274_4512_implies_Equation4364 G eq4274 eq4512
  exact Equation4364_4512_implies_Equation4283 G eq4364 eq4512

theorem Equation314_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4287 := Equation4278_4512_implies_Equation4287 G eq4278 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation314_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation314_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4287 G eq4278 eq4512

theorem Equation314_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation314_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4369 := Equation4274_4512_implies_Equation4369 G eq4274 eq4512
  exact Equation4369_4512_implies_Equation4290 G eq4369 eq4512

theorem Equation314_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4291 G eq4296 eq4512

theorem Equation314_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation314_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation314_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  exact Equation4299_4512_implies_Equation4297 G eq4299 eq4512

theorem Equation314_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4299 G eq4274 eq4512

theorem Equation314_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4300 G eq4278 eq4512

theorem Equation314_4512_implies_Equation4301 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4301 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4301 G eq4274 eq4512

theorem Equation314_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation314_4512_implies_Equation4305 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4305 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4301 := Equation4274_4512_implies_Equation4301 G eq4274 eq4512
  exact Equation4301_4512_implies_Equation4305 G eq4301 eq4512

theorem Equation314_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4314 G eq4318 eq4512

theorem Equation314_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4315 G eq4271 eq4512

theorem Equation314_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4318 G eq4331 eq4512

theorem Equation314_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4364 := Equation4274_4512_implies_Equation4364 G eq4274 eq4512
  exact Equation4364_4512_implies_Equation4320 G eq4364 eq4512

theorem Equation314_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4279 := Equation4331_4512_implies_Equation4279 G eq4331 eq4512
  exact Equation4279_4512_implies_Equation4321 G eq4279 eq4512

theorem Equation314_4512_implies_Equation4325 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4325 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4325 G eq4331 eq4512

theorem Equation314_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4327 G eq4331 eq4512

theorem Equation314_4512_implies_Equation4331 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4331 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4331 G eq4274 eq4512

theorem Equation314_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation314_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4358 G eq4271 eq4512

theorem Equation314_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4362 G eq4278 eq4512

theorem Equation314_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4364 G eq4274 eq4512

theorem Equation314_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq314 : Equation314 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  exact Equation4274_4512_implies_Equation4369 G eq4274 eq4512

theorem Equation315_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation315_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3255 := Equation315_4512_implies_Equation3255 G eq315 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation315_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation315_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3258 G eq312 eq4512

theorem Equation315_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation3261 G eq3271 eq4512

theorem Equation315_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation315_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation315_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation315_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq315 : Equation315 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4284 G eq4304 eq4512

theorem Equation316_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation316_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation315_4512_implies_Equation3255 G eq315 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation316_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation316_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation316_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation316_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation3255 G eq315 eq4512

theorem Equation316_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation316_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation3258 G eq310 eq4512

theorem Equation316_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation316_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation3261 G eq3271 eq4512

theorem Equation316_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation316_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation316_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation316_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4270 G eq4297 eq4512

theorem Equation316_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4272 G eq4304 eq4512

theorem Equation316_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation316_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4276 G eq4277 eq4512

theorem Equation316_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation316_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4280 G eq4299 eq4512

theorem Equation316_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4284 G eq4304 eq4512

theorem Equation316_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4288 G eq4299 eq4512

theorem Equation316_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation316_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation316_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation316_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation316_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq316 : Equation316 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation318_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation318_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation318_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation318_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  exact Equation3274_4512_implies_Equation315 G eq3274 eq4512

theorem Equation318_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation318_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation318_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation318_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation318_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3264 G eq3300 eq4512

theorem Equation318_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation318_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation318_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation318_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation318_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  exact Equation309_4512_implies_Equation4269 G eq309 eq4512

theorem Equation318_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4327 := Equation4278_4512_implies_Equation4327 G eq4278 eq4512
  exact Equation4327_4512_implies_Equation4272 G eq4327 eq4512

theorem Equation318_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4275 G eq4296 eq4512

theorem Equation318_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation318_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4287 G eq4278 eq4512

theorem Equation318_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4291 G eq4296 eq4512

theorem Equation318_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation318_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4300 G eq4278 eq4512

theorem Equation318_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation318_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4327 := Equation4278_4512_implies_Equation4327 G eq4278 eq4512
  exact Equation4327_4512_implies_Equation4320 G eq4327 eq4512

theorem Equation318_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4327 G eq4278 eq4512

theorem Equation318_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq318 : Equation318 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  exact Equation4278_4512_implies_Equation4362 G eq4278 eq4512

theorem Equation323_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq323 : Equation323 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation323_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq323 : Equation323 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation325_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq325 : Equation325 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  exact Equation4314_4512_implies_Equation1 G eq4314 eq4512

theorem Equation325_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq325 : Equation325 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3316 := Equation325_4512_implies_Equation3316 G eq325 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation325_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq325 : Equation325 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq326 := Equation325_4512_implies_Equation326 G eq325 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation325_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq325 : Equation325 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3315 := Equation325_4512_implies_Equation3315 G eq325 eq4512
  exact Equation3315_4512_implies_Equation3319 G eq3315 eq4512

theorem Equation326_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq326 : Equation326 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation326_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq326 : Equation326 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation327_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq325 := Equation327_4512_implies_Equation325 G eq327 eq4512
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  exact Equation4314_4512_implies_Equation1 G eq4314 eq4512

theorem Equation327_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq325 := Equation327_4512_implies_Equation325 G eq327 eq4512
  have eq326 := Equation325_4512_implies_Equation326 G eq325 eq4512
  exact Equation326_4512_implies_Equation307 G eq326 eq4512

theorem Equation327_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq3322 := Equation327_4512_implies_Equation3322 G eq327 eq4512
  exact Equation3322_4512_implies_Equation326 G eq3322 eq4512

theorem Equation327_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation327_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation327_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq308 := Equation327_4512_implies_Equation308 G eq327 eq4512
  exact Equation308_4512_implies_Equation3256 G eq308 eq4512

theorem Equation327_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq3323 := Equation327_4512_implies_Equation3323 G eq327 eq4512
  exact Equation3323_4512_implies_Equation3315 G eq3323 eq4512

theorem Equation327_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq3322 := Equation327_4512_implies_Equation3322 G eq327 eq4512
  exact Equation3322_4512_implies_Equation3316 G eq3322 eq4512

theorem Equation327_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq325 := Equation327_4512_implies_Equation325 G eq327 eq4512
  have eq326 := Equation325_4512_implies_Equation326 G eq325 eq4512
  exact Equation326_4512_implies_Equation3319 G eq326 eq4512

theorem Equation327_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4268 G eq4315 eq4512

theorem Equation327_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq327 : Equation327 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact Equation4315_4512_implies_Equation4314 G eq4315 eq4512

theorem Equation329_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation329_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  have eq3258 := Equation3326_4512_implies_Equation3258 G eq3326 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation329_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation323 G eq3326 eq4512

theorem Equation329_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation326 G eq3322 eq4512

theorem Equation329_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation329_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  exact Equation3322_4512_implies_Equation3255 G eq3322 eq4512

theorem Equation329_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3258 G eq3326 eq4512

theorem Equation329_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation329_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq309 := Equation329_4512_implies_Equation309 G eq329 eq4512
  exact Equation309_4512_implies_Equation3264 G eq309 eq4512

theorem Equation329_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation329_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  exact Equation3326_4512_implies_Equation3316 G eq3326 eq4512

theorem Equation329_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation329_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4269 G eq4287 eq4512

theorem Equation329_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq329 : Equation329 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation332_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4293 := Equation332_4512_implies_Equation4293 G eq332 eq4512
  exact Equation4293_4512_implies_Equation1 G eq4293 eq4512

theorem Equation332_4512_implies_Equation43 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation43 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  exact Equation3342_4512_implies_Equation43 G eq3342 eq4512

theorem Equation332_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation332_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation323 G eq333 eq4512

theorem Equation332_4512_implies_Equation326 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation326 G := by
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation326 G eq325 eq4512

theorem Equation332_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  have eq3306 := Equation3308_4512_implies_Equation3306 G eq3308 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation332_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  exact Equation323_4512_implies_Equation3306 G eq323 eq4512

theorem Equation332_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  exact Equation3342_4512_implies_Equation3308 G eq3342 eq4512

theorem Equation332_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation3315 G eq325 eq4512

theorem Equation332_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation3316 G eq333 eq4512

theorem Equation332_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  have eq3315 := Equation325_4512_implies_Equation3315 G eq325 eq4512
  exact Equation3315_4512_implies_Equation3319 G eq3315 eq4512

theorem Equation332_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  exact Equation3342_4512_implies_Equation3346 G eq3342 eq4512

theorem Equation332_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation3353 G eq333 eq4512

theorem Equation332_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  exact Equation3308_4512_implies_Equation4283 G eq3308 eq4512

theorem Equation332_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3309 := Equation332_4512_implies_Equation3309 G eq332 eq4512
  exact Equation3309_4512_implies_Equation4284 G eq3309 eq4512

theorem Equation332_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact Equation4369_4512_implies_Equation4290 G eq4369 eq4512

theorem Equation332_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  exact Equation333_4512_implies_Equation4291 G eq333 eq4512

theorem Equation332_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  exact Equation325_4512_implies_Equation4314 G eq325 eq4512

theorem Equation332_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq3346 := Equation3342_4512_implies_Equation3346 G eq3342 eq4512
  exact Equation3346_4512_implies_Equation4320 G eq3346 eq4512

theorem Equation332_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4358 G eq43 eq4512

theorem Equation332_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4362 G eq43 eq4512

theorem Equation332_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation332_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq332 : Equation332 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation333_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq333 : Equation333 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4291 := Equation333_4512_implies_Equation4291 G eq333 eq4512
  exact Equation4291_4512_implies_Equation1 G eq4291 eq4512

theorem Equation333_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq333 : Equation333 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation333_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq333 : Equation333 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation333_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq333 : Equation333 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  exact Equation323_4512_implies_Equation3306 G eq323 eq4512

theorem Equation343_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4300 := Equation343_4512_implies_Equation4300 G eq343 eq4512
  have eq4272 := Equation4300_4512_implies_Equation4272 G eq4300 eq4512
  exact Equation4272_4512_implies_Equation1 G eq4272 eq4512

theorem Equation343_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  exact Equation323_4512_implies_Equation307 G eq323 eq4512

theorem Equation343_4512_implies_Equation323 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation323 G := by
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation323 G eq333 eq4512

theorem Equation343_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3414 := Equation343_4512_implies_Equation3414 G eq343 eq4512
  have eq3278 := Equation3414_4512_implies_Equation3278 G eq3414 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation343_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation3258 G eq312 eq4512

theorem Equation343_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation343_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  exact Equation323_4512_implies_Equation3306 G eq323 eq4512

theorem Equation343_4512_implies_Equation3316 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation3316 G := by
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation3316 G eq333 eq4512

theorem Equation343_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation3353 G eq333 eq4512

theorem Equation343_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq312 := Equation343_4512_implies_Equation312 G eq343 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation343_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq343 : Equation343 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  exact Equation333_4512_implies_Equation4291 G eq333 eq4512

theorem Equation419_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation419_4512_implies_Equation8 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation8 G := by
  have eq429 := Equation419_4512_implies_Equation429 G eq419 eq4512
  exact Equation429_4512_implies_Equation8 G eq429 eq4512

theorem Equation419_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq429 := Equation419_4512_implies_Equation429 G eq419 eq4512
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  exact Equation8_4512_implies_Equation411 G eq8 eq4512

theorem Equation419_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation419_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation419_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation419_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq419 : Equation419 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation429_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq429 : Equation429 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation429_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq429 : Equation429 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  exact Equation8_4512_implies_Equation411 G eq8 eq4512

theorem Equation429_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq429 : Equation429 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation429_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq429 : Equation429 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  exact Equation8_4512_implies_Equation3306 G eq8 eq4512

theorem Equation429_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq429 : Equation429 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  exact Equation8_4512_implies_Equation3319 G eq8 eq4512

theorem Equation440_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq440 : Equation440 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation477_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  have eq4290 := Equation504_4512_implies_Equation4290 G eq504 eq4512
  exact Equation4290_4512_implies_Equation1 G eq4290 eq4512

theorem Equation477_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  have eq513 := Equation504_4512_implies_Equation513 G eq504 eq4512
  exact Equation513_4512_implies_Equation411 G eq513 eq4512

theorem Equation477_4512_implies_Equation440 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation440 G := by
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  exact Equation504_4512_implies_Equation440 G eq504 eq4512

theorem Equation477_4512_implies_Equation513 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation513 G := by
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  exact Equation504_4512_implies_Equation513 G eq504 eq4512

theorem Equation477_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation477_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  exact Equation504_4512_implies_Equation4290 G eq504 eq4512

theorem Equation477_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  exact Equation4362_4512_implies_Equation4320 G eq4362 eq4512

theorem Equation477_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4358 G eq43 eq4512

theorem Equation477_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4362 G eq43 eq4512

theorem Equation477_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation477_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq477 : Equation477 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq43 := Equation477_4512_implies_Equation43 G eq477 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation504_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq504 : Equation504 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4290 := Equation504_4512_implies_Equation4290 G eq504 eq4512
  exact Equation4290_4512_implies_Equation1 G eq4290 eq4512

theorem Equation504_4512_implies_Equation411 (G : Type*) [Magma G]
  (eq504 : Equation504 G) (eq4512 : Equation4512 G) : Equation411 G := by
  have eq440 := Equation504_4512_implies_Equation440 G eq504 eq4512
  exact Equation440_4512_implies_Equation411 G eq440 eq4512

theorem Equation513_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq513 : Equation513 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq411 := Equation513_4512_implies_Equation411 G eq513 eq4512
  exact Equation411_4512_implies_Equation1 G eq411 eq4512

theorem Equation3255_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3255 : Equation3255 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq307 := Equation3255_4512_implies_Equation307 G eq3255 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3255_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3255 : Equation3255 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq307 := Equation3255_4512_implies_Equation307 G eq3255 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation3256_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3256 : Equation3256 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3258_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3258 : Equation3258 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3258_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3258 : Equation3258 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation3259_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3259 : Equation3259 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact Equation4270_4512_implies_Equation1 G eq4270 eq4512

theorem Equation3259_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3259 : Equation3259 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3256 := Equation3259_4512_implies_Equation3256 G eq3259 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation3260_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  have eq4268 := Equation4288_4512_implies_Equation4268 G eq4288 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation3260_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3258 := Equation310_4512_implies_Equation3258 G eq310 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation3260_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3260_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation3260_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation3260_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3260_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation3258 G eq310 eq4512

theorem Equation3260_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation3260_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3261 G eq3259 eq4512

theorem Equation3260_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3260_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation3260_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4284 G eq4288 eq4512

theorem Equation3260_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3260 : Equation3260 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3261_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3261 : Equation3261 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3264_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3264 : Equation3264 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation3264_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3264 : Equation3264 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation3264_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3264 : Equation3264 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation3265_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  have eq4268 := Equation4288_4512_implies_Equation4268 G eq4288 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation3265_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3258 := Equation310_4512_implies_Equation3258 G eq310 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation3265_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3265_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation3265_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  exact Equation308_4512_implies_Equation3255 G eq308 eq4512

theorem Equation3265_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3265_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation3258 G eq310 eq4512

theorem Equation3265_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation3265_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3261 G eq3259 eq4512

theorem Equation3265_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3265_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation3265_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4284 G eq4288 eq4512

theorem Equation3265_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3265 : Equation3265 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3267_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation3267_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation3267_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3267_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  exact Equation3260_4512_implies_Equation310 G eq3260 eq4512

theorem Equation3267_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation3267_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation3267_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3267_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation3267_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation3267_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation3267_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3267_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4270 G eq4288 eq4512

theorem Equation3267_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation3267_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3267 : Equation3267 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3271_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3271 : Equation3271 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation3271_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3271 : Equation3271 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3273_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  have eq4268 := Equation4288_4512_implies_Equation4268 G eq4288 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation3273_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  exact Equation316_4512_implies_Equation40 G eq316 eq4512

theorem Equation3273_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3258 := Equation310_4512_implies_Equation3258 G eq310 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation3273_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3273_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation3273_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3273_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation3273_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3273_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation3255 G eq315 eq4512

theorem Equation3273_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3273_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation3258 G eq310 eq4512

theorem Equation3273_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation3273_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3261 G eq3259 eq4512

theorem Equation3273_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3271 G eq40 eq4512

theorem Equation3273_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3273_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3273_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4270 G eq4288 eq4512

theorem Equation3273_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4272 G eq4304 eq4512

theorem Equation3273_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3273_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4276 G eq4277 eq4512

theorem Equation3273_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation3273_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4280 G eq4299 eq4512

theorem Equation3273_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4284 G eq4288 eq4512

theorem Equation3273_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq3260 := Equation3273_4512_implies_Equation3260 G eq3273 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3273_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation3273_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation3273_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation3273_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  exact Equation316_4512_implies_Equation4299 G eq316 eq4512

theorem Equation3273_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3273_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq3273 : Equation3273 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation3274_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation3274_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3255 := Equation315_4512_implies_Equation3255 G eq315 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation3274_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3274_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3274_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation3255 G eq315 eq4512

theorem Equation3274_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3258 G eq312 eq4512

theorem Equation3274_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation3261 G eq3271 eq4512

theorem Equation3274_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation3274_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3274_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation3274_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3274_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4284 G eq4304 eq4512

theorem Equation3274_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3274 : Equation3274 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3275_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation3275_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation40 G eq316 eq4512

theorem Equation3275_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation3275_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3275_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation3275_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3275_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation315 G eq316 eq4512

theorem Equation3275_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation3275_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation3275_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3275_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation3275_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation3275_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation3275_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3271 G eq40 eq4512

theorem Equation3275_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3275_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3275_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4270 G eq4280 eq4512

theorem Equation3275_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation3275_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3275_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation3275_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation3275_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4280 G eq4299 eq4512

theorem Equation3275_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3264 := Equation3275_4512_implies_Equation3264 G eq3275 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation3275_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3275_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation3275_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation3275_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation3275_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation4299 G eq316 eq4512

theorem Equation3275_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3275_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq3275 : Equation3275 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation3277_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation3277_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation40 G eq316 eq4512

theorem Equation3277_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation3277_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3277_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation3277_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3277_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation3277_4512_implies_Equation316 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation316 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  exact Equation3275_4512_implies_Equation316 G eq3275 eq4512

theorem Equation3277_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation3277_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation3277_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3277_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation3277_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation3259 G eq310 eq4512

theorem Equation3277_4512_implies_Equation3260 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3260 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  exact Equation3267_4512_implies_Equation3260 G eq3267 eq4512

theorem Equation3277_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation3277_4512_implies_Equation3264 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3264 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact Equation3300_4512_implies_Equation3264 G eq3300 eq4512

theorem Equation3277_4512_implies_Equation3265 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3265 G := by
  have eq3290 := Equation3277_4512_implies_Equation3290 G eq3277 eq4512
  exact Equation3290_4512_implies_Equation3265 G eq3290 eq4512

theorem Equation3277_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation3277_4512_implies_Equation3274 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3274 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact Equation3300_4512_implies_Equation3274 G eq3300 eq4512

theorem Equation3277_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3277_4512_implies_Equation3292 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation3292 G := by
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact Equation3300_4512_implies_Equation3292 G eq3300 eq4512

theorem Equation3277_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3277_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4270 G eq4280 eq4512

theorem Equation3277_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation3277_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3277_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation3277_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation3277_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4280 G eq4299 eq4512

theorem Equation3277_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation3277_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq3267 := Equation3277_4512_implies_Equation3267 G eq3277 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3277_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation3277_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation3277_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation3277_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  exact Equation316_4512_implies_Equation4299 G eq316 eq4512

theorem Equation3277_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3277_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq3277 : Equation3277 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation3278_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3278 : Equation3278 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3253 := Equation3278_4512_implies_Equation3253 G eq3278 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3290_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation3290_4512_implies_Equation40 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation40 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  exact Equation316_4512_implies_Equation40 G eq316 eq4512

theorem Equation3290_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation315_4512_implies_Equation3255 G eq315 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation3290_4512_implies_Equation308 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation308 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation308 G eq310 eq4512

theorem Equation3290_4512_implies_Equation310 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation310 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  exact Equation316_4512_implies_Equation310 G eq316 eq4512

theorem Equation3290_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3290_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  exact Equation316_4512_implies_Equation315 G eq316 eq4512

theorem Equation3290_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3290_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation3255 G eq315 eq4512

theorem Equation3290_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3290_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation3258 G eq310 eq4512

theorem Equation3290_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation3290_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation3261 G eq3271 eq4512

theorem Equation3290_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation3271 G eq40 eq4512

theorem Equation3290_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3290_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation3290_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4270 G eq4297 eq4512

theorem Equation3290_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4272 G eq4304 eq4512

theorem Equation3290_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3290_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4276 G eq4277 eq4512

theorem Equation3290_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation3290_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  exact Equation4299_4512_implies_Equation4280 G eq4299 eq4512

theorem Equation3290_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4284 G eq4304 eq4512

theorem Equation3290_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  exact Equation310_4512_implies_Equation4288 G eq310 eq4512

theorem Equation3290_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation3290_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation3290_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq40 := Equation316_4512_implies_Equation40 G eq316 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation3290_4512_implies_Equation4299 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4299 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  exact Equation316_4512_implies_Equation4299 G eq316 eq4512

theorem Equation3290_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3290_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq3290 : Equation3290 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation3292_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation3292_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3255 := Equation315_4512_implies_Equation3255 G eq315 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation3292_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3292_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3292_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation3255 G eq315 eq4512

theorem Equation3292_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3258 G eq312 eq4512

theorem Equation3292_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation3261 G eq3271 eq4512

theorem Equation3292_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation3292_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3292_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation4272 G eq312 eq4512

theorem Equation3292_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3292_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4284 G eq4304 eq4512

theorem Equation3292_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3292 : Equation3292 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3300_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation3300_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  exact Equation3255_4512_implies_Equation307 G eq3255 eq4512

theorem Equation3300_4512_implies_Equation312 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation312 G := by
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  exact Equation315_4512_implies_Equation312 G eq315 eq4512

theorem Equation3300_4512_implies_Equation315 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation315 G := by
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  exact Equation3292_4512_implies_Equation315 G eq3292 eq4512

theorem Equation3300_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  exact Equation3261_4512_implies_Equation3253 G eq3261 eq4512

theorem Equation3300_4512_implies_Equation3255 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation3255 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation3255 G eq3264 eq4512

theorem Equation3300_4512_implies_Equation3258 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation3258 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation3258 G eq3264 eq4512

theorem Equation3300_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation3261 G eq3264 eq4512

theorem Equation3300_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation3271 G eq315 eq4512

theorem Equation3300_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  exact Equation312_4512_implies_Equation3278 G eq312 eq4512

theorem Equation3300_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact Equation4304_4512_implies_Equation4272 G eq4304 eq4512

theorem Equation3300_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3300_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  exact Equation3264_4512_implies_Equation4284 G eq3264 eq4512

theorem Equation3300_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq3300 : Equation3300 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  exact Equation315_4512_implies_Equation4304 G eq315 eq4512

theorem Equation3306_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3306 : Equation3306 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3308_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3308 : Equation3308 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4283 := Equation3308_4512_implies_Equation4283 G eq3308 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation3308_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3308 : Equation3308 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3306 := Equation3308_4512_implies_Equation3306 G eq3308 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3308_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3308 : Equation3308 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  exact Equation3315_4512_implies_Equation3319 G eq3315 eq4512

theorem Equation3309_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3309 : Equation3309 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4284 := Equation3309_4512_implies_Equation4284 G eq3309 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation3309_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3309 : Equation3309 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3316 := Equation3309_4512_implies_Equation3316 G eq3309 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation3309_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3309 : Equation3309 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq323 := Equation3309_4512_implies_Equation323 G eq3309 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation3309_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3309 : Equation3309 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq323 := Equation3309_4512_implies_Equation323 G eq3309 eq4512
  exact Equation323_4512_implies_Equation3306 G eq323 eq4512

theorem Equation3309_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3309 : Equation3309 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq326 := Equation3309_4512_implies_Equation326 G eq3309 eq4512
  exact Equation326_4512_implies_Equation3319 G eq326 eq4512

theorem Equation3315_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3315 : Equation3315 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3315_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3315 : Equation3315 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact Equation3319_4512_implies_Equation3253 G eq3319 eq4512

theorem Equation3316_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3316 : Equation3316 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq307 := Equation3316_4512_implies_Equation307 G eq3316 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3316_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3316 : Equation3316 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq307 := Equation3316_4512_implies_Equation307 G eq3316 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation3319_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3319 : Equation3319 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3322_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3322 : Equation3322 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq326 := Equation3322_4512_implies_Equation326 G eq3322 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3322_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3322 : Equation3322 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3316 := Equation3322_4512_implies_Equation3316 G eq3322 eq4512
  exact Equation3316_4512_implies_Equation307 G eq3316 eq4512

theorem Equation3322_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3322 : Equation3322 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq326 := Equation3322_4512_implies_Equation326 G eq3322 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation3322_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3322 : Equation3322 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq326 := Equation3322_4512_implies_Equation326 G eq3322 eq4512
  exact Equation326_4512_implies_Equation3319 G eq326 eq4512

theorem Equation3323_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3323 : Equation3323 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3256 := Equation3323_4512_implies_Equation3256 G eq3323 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3323_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3323 : Equation3323 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3256 := Equation3323_4512_implies_Equation3256 G eq3323 eq4512
  exact Equation3256_4512_implies_Equation3253 G eq3256 eq4512

theorem Equation3323_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3323 : Equation3323 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3315 := Equation3323_4512_implies_Equation3315 G eq3323 eq4512
  exact Equation3315_4512_implies_Equation3319 G eq3315 eq4512

theorem Equation3326_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3326 : Equation3326 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq323 := Equation3326_4512_implies_Equation323 G eq3326 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3326_4512_implies_Equation307 (G : Type*) [Magma G]
  (eq3326 : Equation3326 G) (eq4512 : Equation4512 G) : Equation307 G := by
  have eq3258 := Equation3326_4512_implies_Equation3258 G eq3326 eq4512
  exact Equation3258_4512_implies_Equation307 G eq3258 eq4512

theorem Equation3326_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3326 : Equation3326 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq323 := Equation3326_4512_implies_Equation323 G eq3326 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  exact Equation307_4512_implies_Equation3253 G eq307 eq4512

theorem Equation3326_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3326 : Equation3326 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq323 := Equation3326_4512_implies_Equation323 G eq3326 eq4512
  exact Equation323_4512_implies_Equation3306 G eq323 eq4512

theorem Equation3331_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation3331_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3331_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3331_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation3331_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation3331_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation3331_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation3331_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  exact Equation3259_4512_implies_Equation4270 G eq3259 eq4512

theorem Equation3331_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq3331 : Equation3331 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  exact Equation4358_4512_implies_Equation4283 G eq4358 eq4512

theorem Equation3334_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3334 : Equation3334 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3334_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3334 : Equation3334 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3342_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  have eq4283 := Equation3308_4512_implies_Equation4283 G eq3308 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation3342_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  have eq3306 := Equation3308_4512_implies_Equation3306 G eq3308 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3342_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  exact Equation3308_4512_implies_Equation3306 G eq3308 eq4512

theorem Equation3342_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation3342_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3346 := Equation3342_4512_implies_Equation3346 G eq3342 eq4512
  exact Equation3346_4512_implies_Equation3319 G eq3346 eq4512

theorem Equation3342_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq3346 := Equation3342_4512_implies_Equation3346 G eq3342 eq4512
  exact Equation3346_4512_implies_Equation3353 G eq3346 eq4512

theorem Equation3342_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  exact Equation3308_4512_implies_Equation4283 G eq3308 eq4512

theorem Equation3342_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  exact Equation4364_4512_implies_Equation4290 G eq4364 eq4512

theorem Equation3342_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq3346 := Equation3342_4512_implies_Equation3346 G eq3342 eq4512
  exact Equation3346_4512_implies_Equation4320 G eq3346 eq4512

theorem Equation3342_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4358 G eq43 eq4512

theorem Equation3342_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4362 G eq43 eq4512

theorem Equation3342_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation3342_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq3342 : Equation3342 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation3346_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3346 : Equation3346 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4320 := Equation3346_4512_implies_Equation4320 G eq3346 eq4512
  exact Equation4320_4512_implies_Equation1 G eq4320 eq4512

theorem Equation3346_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3346 : Equation3346 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3319 := Equation3346_4512_implies_Equation3319 G eq3346 eq4512
  exact Equation3319_4512_implies_Equation3253 G eq3319 eq4512

theorem Equation3346_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3346 : Equation3346 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  exact Equation3353_4512_implies_Equation3306 G eq3353 eq4512

theorem Equation3350_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation3350_4512_implies_Equation43 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation43 G := by
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  exact Equation3342_4512_implies_Equation43 G eq3342 eq4512

theorem Equation3350_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3350_4512_implies_Equation3256 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3256 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  exact Equation3259_4512_implies_Equation3256 G eq3259 eq4512

theorem Equation3350_4512_implies_Equation3259 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3259 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation3259 G eq40 eq4512

theorem Equation3350_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation3350_4512_implies_Equation3271 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3271 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation3271 G eq40 eq4512

theorem Equation3350_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation3350_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation3350_4512_implies_Equation3308 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3308 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  exact Equation3331_4512_implies_Equation3308 G eq3331 eq4512

theorem Equation3350_4512_implies_Equation3315 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3315 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  exact Equation3308_4512_implies_Equation3315 G eq3308 eq4512

theorem Equation3350_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation3350_4512_implies_Equation3323 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3323 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  exact Equation3331_4512_implies_Equation3323 G eq3331 eq4512

theorem Equation3350_4512_implies_Equation3334 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3334 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  exact Equation3331_4512_implies_Equation3334 G eq3331 eq4512

theorem Equation3350_4512_implies_Equation3346 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3346 G := by
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  exact Equation3342_4512_implies_Equation3346 G eq3342 eq4512

theorem Equation3350_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  have eq3346 := Equation3342_4512_implies_Equation3346 G eq3342 eq4512
  exact Equation3346_4512_implies_Equation3353 G eq3346 eq4512

theorem Equation3350_4512_implies_Equation3414 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation3414 G := by
  have eq3388 := Equation3350_4512_implies_Equation3388 G eq3350 eq4512
  exact Equation3388_4512_implies_Equation3414 G eq3388 eq4512

theorem Equation3350_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4270 G eq4325 eq4512

theorem Equation3350_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation3350_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4275 G eq4305 eq4512

theorem Equation3350_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  exact Equation4305_4512_implies_Equation4283 G eq4305 eq4512

theorem Equation3350_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation3350_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq40 := Equation3350_4512_implies_Equation40 G eq3350 eq4512
  exact Equation40_4512_implies_Equation4297 G eq40 eq4512

theorem Equation3350_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  exact Equation4325_4512_implies_Equation4320 G eq4325 eq4512

theorem Equation3350_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  exact Equation3331_4512_implies_Equation4358 G eq3331 eq4512

theorem Equation3350_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq3388 := Equation3350_4512_implies_Equation3388 G eq3350 eq4512
  exact Equation3388_4512_implies_Equation4362 G eq3388 eq4512

theorem Equation3350_4512_implies_Equation4364 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4364 G := by
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4364 G eq43 eq4512

theorem Equation3350_4512_implies_Equation4369 (G : Type*) [Magma G]
  (eq3350 : Equation3350 G) (eq4512 : Equation4512 G) : Equation4369 G := by
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  have eq43 := Equation3342_4512_implies_Equation43 G eq3342 eq4512
  exact Equation43_4512_implies_Equation4369 G eq43 eq4512

theorem Equation3353_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3353 : Equation3353 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3306 := Equation3353_4512_implies_Equation3306 G eq3353 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3353_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3353 : Equation3353 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3306 := Equation3353_4512_implies_Equation3306 G eq3353 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3388_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation3388_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3334 := Equation3388_4512_implies_Equation3334 G eq3388 eq4512
  have eq3306 := Equation3334_4512_implies_Equation3306 G eq3334 eq4512
  exact Equation3306_4512_implies_Equation3253 G eq3306 eq4512

theorem Equation3388_4512_implies_Equation3261 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation3261 G := by
  have eq3334 := Equation3388_4512_implies_Equation3334 G eq3388 eq4512
  exact Equation3334_4512_implies_Equation3261 G eq3334 eq4512

theorem Equation3388_4512_implies_Equation3278 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation3278 G := by
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation3278 G eq3271 eq4512

theorem Equation3388_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3334 := Equation3388_4512_implies_Equation3334 G eq3388 eq4512
  exact Equation3334_4512_implies_Equation3306 G eq3334 eq4512

theorem Equation3388_4512_implies_Equation3319 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation3319 G := by
  have eq3334 := Equation3388_4512_implies_Equation3334 G eq3388 eq4512
  exact Equation3334_4512_implies_Equation3319 G eq3334 eq4512

theorem Equation3388_4512_implies_Equation3353 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation3353 G := by
  have eq3346 := Equation3388_4512_implies_Equation3346 G eq3388 eq4512
  exact Equation3346_4512_implies_Equation3353 G eq3346 eq4512

theorem Equation3388_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq3271 := Equation3388_4512_implies_Equation3271 G eq3388 eq4512
  exact Equation3271_4512_implies_Equation4275 G eq3271 eq4512

theorem Equation3388_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq3388 : Equation3388 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4362 := Equation3388_4512_implies_Equation4362 G eq3388 eq4512
  exact Equation4362_4512_implies_Equation4320 G eq4362 eq4512

theorem Equation3414_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq3414 : Equation3414 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq3278 := Equation3414_4512_implies_Equation3278 G eq3414 eq4512
  have eq3253 := Equation3278_4512_implies_Equation3253 G eq3278 eq4512
  exact Equation3253_4512_implies_Equation1 G eq3253 eq4512

theorem Equation3414_4512_implies_Equation3253 (G : Type*) [Magma G]
  (eq3414 : Equation3414 G) (eq4512 : Equation4512 G) : Equation3253 G := by
  have eq3278 := Equation3414_4512_implies_Equation3278 G eq3414 eq4512
  exact Equation3278_4512_implies_Equation3253 G eq3278 eq4512

theorem Equation3414_4512_implies_Equation3306 (G : Type*) [Magma G]
  (eq3414 : Equation3414 G) (eq4512 : Equation4512 G) : Equation3306 G := by
  have eq3353 := Equation3414_4512_implies_Equation3353 G eq3414 eq4512
  exact Equation3353_4512_implies_Equation3306 G eq3353 eq4512

theorem Equation4271_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4288 := Equation4271_4512_implies_Equation4288 G eq4271 eq4512
  have eq4268 := Equation4288_4512_implies_Equation4268 G eq4288 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation4271_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4286 := Equation4271_4512_implies_Equation4286 G eq4271 eq4512
  exact Equation4286_4512_implies_Equation4268 G eq4286 eq4512

theorem Equation4271_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq4318 := Equation4271_4512_implies_Equation4318 G eq4271 eq4512
  exact Equation4318_4512_implies_Equation4269 G eq4318 eq4512

theorem Equation4271_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4318 := Equation4271_4512_implies_Equation4318 G eq4271 eq4512
  exact Equation4318_4512_implies_Equation4270 G eq4318 eq4512

theorem Equation4271_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4286 := Equation4271_4512_implies_Equation4286 G eq4271 eq4512
  exact Equation4286_4512_implies_Equation4283 G eq4286 eq4512

theorem Equation4271_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4287 := Equation4271_4512_implies_Equation4287 G eq4271 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation4271_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq4271 : Equation4271 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4318 := Equation4271_4512_implies_Equation4318 G eq4271 eq4512
  exact Equation4318_4512_implies_Equation4314 G eq4318 eq4512

theorem Equation4274_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4364 := Equation4274_4512_implies_Equation4364 G eq4274 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact Equation4320_4512_implies_Equation1 G eq4320 eq4512

theorem Equation4274_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  have eq4286 := Equation4271_4512_implies_Equation4286 G eq4271 eq4512
  exact Equation4286_4512_implies_Equation4268 G eq4286 eq4512

theorem Equation4274_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq4301 := Equation4274_4512_implies_Equation4301 G eq4274 eq4512
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  exact Equation4296_4512_implies_Equation4269 G eq4296 eq4512

theorem Equation4274_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4270 G eq4318 eq4512

theorem Equation4274_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4327 := Equation4331_4512_implies_Equation4327 G eq4331 eq4512
  exact Equation4327_4512_implies_Equation4272 G eq4327 eq4512

theorem Equation4274_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq4301 := Equation4274_4512_implies_Equation4301 G eq4274 eq4512
  have eq4305 := Equation4301_4512_implies_Equation4305 G eq4301 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation4274_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4275 G eq4296 eq4512

theorem Equation4274_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation4274_4512_implies_Equation4277 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4277 G := by
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  exact Equation4299_4512_implies_Equation4277 G eq4299 eq4512

theorem Equation4274_4512_implies_Equation4279 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4279 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4279 G eq4331 eq4512

theorem Equation4274_4512_implies_Equation4280 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4280 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4280 G eq4331 eq4512

theorem Equation4274_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4364 := Equation4274_4512_implies_Equation4364 G eq4274 eq4512
  exact Equation4364_4512_implies_Equation4283 G eq4364 eq4512

theorem Equation4274_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  have eq4287 := Equation4278_4512_implies_Equation4287 G eq4278 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation4274_4512_implies_Equation4286 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4286 G := by
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4286 G eq4271 eq4512

theorem Equation4274_4512_implies_Equation4287 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4287 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  exact Equation4278_4512_implies_Equation4287 G eq4278 eq4512

theorem Equation4274_4512_implies_Equation4288 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4288 G := by
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4288 G eq4271 eq4512

theorem Equation4274_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq4369 := Equation4274_4512_implies_Equation4369 G eq4274 eq4512
  exact Equation4369_4512_implies_Equation4290 G eq4369 eq4512

theorem Equation4274_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4291 G eq4296 eq4512

theorem Equation4274_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation4274_4512_implies_Equation4296 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4296 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  exact Equation4278_4512_implies_Equation4296 G eq4278 eq4512

theorem Equation4274_4512_implies_Equation4297 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4297 G := by
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  exact Equation4299_4512_implies_Equation4297 G eq4299 eq4512

theorem Equation4274_4512_implies_Equation4300 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4300 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  exact Equation4278_4512_implies_Equation4300 G eq4278 eq4512

theorem Equation4274_4512_implies_Equation4304 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4304 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  exact Equation4278_4512_implies_Equation4304 G eq4278 eq4512

theorem Equation4274_4512_implies_Equation4305 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4305 G := by
  have eq4301 := Equation4274_4512_implies_Equation4301 G eq4274 eq4512
  exact Equation4301_4512_implies_Equation4305 G eq4301 eq4512

theorem Equation4274_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4314 G eq4318 eq4512

theorem Equation4274_4512_implies_Equation4315 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4315 G := by
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4315 G eq4271 eq4512

theorem Equation4274_4512_implies_Equation4318 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4318 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4318 G eq4331 eq4512

theorem Equation4274_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4364 := Equation4274_4512_implies_Equation4364 G eq4274 eq4512
  exact Equation4364_4512_implies_Equation4320 G eq4364 eq4512

theorem Equation4274_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4279 := Equation4331_4512_implies_Equation4279 G eq4331 eq4512
  exact Equation4279_4512_implies_Equation4321 G eq4279 eq4512

theorem Equation4274_4512_implies_Equation4325 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4325 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4325 G eq4331 eq4512

theorem Equation4274_4512_implies_Equation4327 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4327 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  exact Equation4331_4512_implies_Equation4327 G eq4331 eq4512

theorem Equation4274_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation4274_4512_implies_Equation4358 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4358 G := by
  have eq4271 := Equation4274_4512_implies_Equation4271 G eq4274 eq4512
  exact Equation4271_4512_implies_Equation4358 G eq4271 eq4512

theorem Equation4274_4512_implies_Equation4362 (G : Type*) [Magma G]
  (eq4274 : Equation4274 G) (eq4512 : Equation4512 G) : Equation4362 G := by
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  exact Equation4278_4512_implies_Equation4362 G eq4278 eq4512

theorem Equation4277_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4277 : Equation4277 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4275 := Equation4277_4512_implies_Equation4275 G eq4277 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation4278_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4327 := Equation4278_4512_implies_Equation4327 G eq4278 eq4512
  have eq4272 := Equation4327_4512_implies_Equation4272 G eq4327 eq4512
  exact Equation4272_4512_implies_Equation1 G eq4272 eq4512

theorem Equation4278_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq4287 := Equation4278_4512_implies_Equation4287 G eq4278 eq4512
  exact Equation4287_4512_implies_Equation4269 G eq4287 eq4512

theorem Equation4278_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq4327 := Equation4278_4512_implies_Equation4327 G eq4278 eq4512
  exact Equation4327_4512_implies_Equation4272 G eq4327 eq4512

theorem Equation4278_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4275 G eq4296 eq4512

theorem Equation4278_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4287 := Equation4278_4512_implies_Equation4287 G eq4278 eq4512
  exact Equation4287_4512_implies_Equation4284 G eq4287 eq4512

theorem Equation4278_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  exact Equation4296_4512_implies_Equation4291 G eq4296 eq4512

theorem Equation4278_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq4278 : Equation4278 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4327 := Equation4278_4512_implies_Equation4327 G eq4278 eq4512
  exact Equation4327_4512_implies_Equation4320 G eq4327 eq4512

theorem Equation4279_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4279 : Equation4279 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4269 := Equation4279_4512_implies_Equation4269 G eq4279 eq4512
  exact Equation4269_4512_implies_Equation1 G eq4269 eq4512

theorem Equation4280_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4280 : Equation4280 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4270 := Equation4280_4512_implies_Equation4270 G eq4280 eq4512
  exact Equation4270_4512_implies_Equation1 G eq4270 eq4512

theorem Equation4286_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4286 : Equation4286 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation4287_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4287 : Equation4287 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4284 := Equation4287_4512_implies_Equation4284 G eq4287 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation4288_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4288 : Equation4288 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  exact Equation4284_4512_implies_Equation1 G eq4284 eq4512

theorem Equation4296_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4296 : Equation4296 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4275 := Equation4296_4512_implies_Equation4275 G eq4296 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation4297_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4297 : Equation4297 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4275 := Equation4297_4512_implies_Equation4275 G eq4297 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation4299_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  have eq4268 := Equation4288_4512_implies_Equation4268 G eq4288 eq4512
  exact Equation4268_4512_implies_Equation1 G eq4268 eq4512

theorem Equation4299_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  exact Equation4288_4512_implies_Equation4268 G eq4288 eq4512

theorem Equation4299_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4270 G eq4280 eq4512

theorem Equation4299_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4272 G eq4280 eq4512

theorem Equation4299_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4304 := Equation4299_4512_implies_Equation4304 G eq4299 eq4512
  exact Equation4304_4512_implies_Equation4275 G eq4304 eq4512

theorem Equation4299_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation4299_4512_implies_Equation4284 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4284 G := by
  have eq4304 := Equation4299_4512_implies_Equation4304 G eq4299 eq4512
  exact Equation4304_4512_implies_Equation4284 G eq4304 eq4512

theorem Equation4299_4512_implies_Equation4290 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4290 G := by
  have eq4297 := Equation4299_4512_implies_Equation4297 G eq4299 eq4512
  exact Equation4297_4512_implies_Equation4290 G eq4297 eq4512

theorem Equation4299_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation4299_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq4299 : Equation4299 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation4300_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4300 : Equation4300 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4272 := Equation4300_4512_implies_Equation4272 G eq4300 eq4512
  exact Equation4272_4512_implies_Equation1 G eq4272 eq4512

theorem Equation4301_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  have eq4275 := Equation4296_4512_implies_Equation4275 G eq4296 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation4301_4512_implies_Equation4268 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4268 G := by
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  exact Equation4286_4512_implies_Equation4268 G eq4286 eq4512

theorem Equation4301_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  exact Equation4286_4512_implies_Equation4269 G eq4286 eq4512

theorem Equation4301_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq4305 := Equation4301_4512_implies_Equation4305 G eq4301 eq4512
  exact Equation4305_4512_implies_Equation4273 G eq4305 eq4512

theorem Equation4301_4512_implies_Equation4275 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4275 G := by
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  exact Equation4296_4512_implies_Equation4275 G eq4296 eq4512

theorem Equation4301_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4277 := Equation4301_4512_implies_Equation4277 G eq4301 eq4512
  exact Equation4277_4512_implies_Equation4276 G eq4277 eq4512

theorem Equation4301_4512_implies_Equation4283 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4283 G := by
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  exact Equation4286_4512_implies_Equation4283 G eq4286 eq4512

theorem Equation4301_4512_implies_Equation4291 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4291 G := by
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  exact Equation4296_4512_implies_Equation4291 G eq4296 eq4512

theorem Equation4301_4512_implies_Equation4293 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4293 G := by
  have eq4277 := Equation4301_4512_implies_Equation4277 G eq4301 eq4512
  exact Equation4277_4512_implies_Equation4293 G eq4277 eq4512

theorem Equation4301_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq4301 : Equation4301 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq4279 := Equation4301_4512_implies_Equation4279 G eq4301 eq4512
  exact Equation4279_4512_implies_Equation4321 G eq4279 eq4512

theorem Equation4304_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4304 : Equation4304 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4275 := Equation4304_4512_implies_Equation4275 G eq4304 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation4305_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4305 : Equation4305 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4275 := Equation4305_4512_implies_Equation4275 G eq4305 eq4512
  exact Equation4275_4512_implies_Equation1 G eq4275 eq4512

theorem Equation4315_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4315 : Equation4315 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4314 := Equation4315_4512_implies_Equation4314 G eq4315 eq4512
  exact Equation4314_4512_implies_Equation1 G eq4314 eq4512

theorem Equation4318_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4318 : Equation4318 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  exact Equation4314_4512_implies_Equation1 G eq4314 eq4512

theorem Equation4325_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4325 : Equation4325 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4270 := Equation4325_4512_implies_Equation4270 G eq4325 eq4512
  exact Equation4270_4512_implies_Equation1 G eq4270 eq4512

theorem Equation4327_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4327 : Equation4327 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  exact Equation4320_4512_implies_Equation1 G eq4320 eq4512

theorem Equation4331_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4325 := Equation4331_4512_implies_Equation4325 G eq4331 eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  exact Equation4320_4512_implies_Equation1 G eq4320 eq4512

theorem Equation4331_4512_implies_Equation4269 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4269 G := by
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4269 G eq4318 eq4512

theorem Equation4331_4512_implies_Equation4270 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4270 G := by
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4270 G eq4318 eq4512

theorem Equation4331_4512_implies_Equation4272 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4272 G := by
  have eq4327 := Equation4331_4512_implies_Equation4327 G eq4331 eq4512
  exact Equation4327_4512_implies_Equation4272 G eq4327 eq4512

theorem Equation4331_4512_implies_Equation4273 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4273 G := by
  have eq4325 := Equation4331_4512_implies_Equation4325 G eq4331 eq4512
  exact Equation4325_4512_implies_Equation4273 G eq4325 eq4512

theorem Equation4331_4512_implies_Equation4276 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4276 G := by
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4276 G eq4280 eq4512

theorem Equation4331_4512_implies_Equation4314 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4314 G := by
  have eq4318 := Equation4331_4512_implies_Equation4318 G eq4331 eq4512
  exact Equation4318_4512_implies_Equation4314 G eq4318 eq4512

theorem Equation4331_4512_implies_Equation4320 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4320 G := by
  have eq4327 := Equation4331_4512_implies_Equation4327 G eq4331 eq4512
  exact Equation4327_4512_implies_Equation4320 G eq4327 eq4512

theorem Equation4331_4512_implies_Equation4321 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4321 G := by
  have eq4279 := Equation4331_4512_implies_Equation4279 G eq4331 eq4512
  exact Equation4279_4512_implies_Equation4321 G eq4279 eq4512

theorem Equation4331_4512_implies_Equation4343 (G : Type*) [Magma G]
  (eq4331 : Equation4331 G) (eq4512 : Equation4512 G) : Equation4343 G := by
  have eq4280 := Equation4331_4512_implies_Equation4280 G eq4331 eq4512
  exact Equation4280_4512_implies_Equation4343 G eq4280 eq4512

theorem Equation4358_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4358 : Equation4358 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation4362_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4362 : Equation4362 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact Equation4320_4512_implies_Equation1 G eq4320 eq4512

theorem Equation4364_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4364 : Equation4364 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  exact Equation4283_4512_implies_Equation1 G eq4283 eq4512

theorem Equation4369_4512_implies_Equation1 (G : Type*) [Magma G]
  (eq4369 : Equation4369 G) (eq4512 : Equation4512 G) : Equation1 G := by
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact Equation4290_4512_implies_Equation1 G eq4290 eq4512

