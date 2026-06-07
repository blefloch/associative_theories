import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.ConjecturesOneImpli
import associative_theories.ConjecturesTwo
import associative_theories.OneImpliDeduced

/- Generated file proving equivalence of conjunction representatives -/

open Conjectures


theorem AT1_implies_long (G : Type*) [Magma G] (h : AssociativeTheory1 G) : AssociativeTheory1_long G := by
  constructor
  rw [Equation1]; intros; rfl
  exact h

theorem AT1_implied_by_long (G : Type*) [Magma G] : AssociativeTheory1_long G -> AssociativeTheory1 G :=
fun ⟨_, h4512⟩ => h4512

theorem AT1_equiv (G : Type*) [Magma G] : AssociativeTheory1 G <-> AssociativeTheory1_long G :=
Iff.intro (AT1_implies_long G) (AT1_implied_by_long G)

theorem AT2_implies_long (G : Type*) [Magma G] (h : AssociativeTheory2 G) : AssociativeTheory2_long G := by
  obtain ⟨eq2, eq4512⟩ := h
  have eq1 := Equation2_4512_implies_Equation1 G eq2 eq4512
  have eq3 := Equation2_4512_implies_Equation3 G eq2 eq4512
  have eq4 := Equation2_4512_implies_Equation4 G eq2 eq4512
  have eq5 := Equation2_4512_implies_Equation5 G eq2 eq4512
  have eq8 := Equation2_4512_implies_Equation8 G eq2 eq4512
  have eq10 := Equation2_4512_implies_Equation10 G eq2 eq4512
  have eq11 := Equation2_4512_implies_Equation11 G eq2 eq4512
  have eq14 := Equation2_4512_implies_Equation14 G eq2 eq4512
  have eq16 := Equation2_4512_implies_Equation16 G eq2 eq4512
  have eq38 := Equation2_4512_implies_Equation38 G eq2 eq4512
  have eq39 := Equation2_4512_implies_Equation39 G eq2 eq4512
  have eq40 := Equation2_4512_implies_Equation40 G eq2 eq4512
  have eq41 := Equation2_4512_implies_Equation41 G eq2 eq4512
  have eq43 := Equation2_4512_implies_Equation43 G eq2 eq4512
  have eq47 := Equation2_4512_implies_Equation47 G eq2 eq4512
  have eq56 := Equation2_4512_implies_Equation56 G eq2 eq4512
  have eq66 := Equation2_4512_implies_Equation66 G eq2 eq4512
  have eq75 := Equation2_4512_implies_Equation75 G eq2 eq4512
  have eq307 := Equation2_4512_implies_Equation307 G eq2 eq4512
  have eq308 := Equation2_4512_implies_Equation308 G eq2 eq4512
  have eq309 := Equation2_4512_implies_Equation309 G eq2 eq4512
  have eq310 := Equation2_4512_implies_Equation310 G eq2 eq4512
  have eq311 := Equation2_4512_implies_Equation311 G eq2 eq4512
  have eq312 := Equation2_4512_implies_Equation312 G eq2 eq4512
  have eq313 := Equation2_4512_implies_Equation313 G eq2 eq4512
  have eq314 := Equation2_4512_implies_Equation314 G eq2 eq4512
  have eq315 := Equation2_4512_implies_Equation315 G eq2 eq4512
  have eq316 := Equation2_4512_implies_Equation316 G eq2 eq4512
  have eq318 := Equation2_4512_implies_Equation318 G eq2 eq4512
  have eq323 := Equation2_4512_implies_Equation323 G eq2 eq4512
  have eq325 := Equation2_4512_implies_Equation325 G eq2 eq4512
  have eq326 := Equation2_4512_implies_Equation326 G eq2 eq4512
  have eq327 := Equation2_4512_implies_Equation327 G eq2 eq4512
  have eq329 := Equation2_4512_implies_Equation329 G eq2 eq4512
  have eq332 := Equation2_4512_implies_Equation332 G eq2 eq4512
  have eq333 := Equation2_4512_implies_Equation333 G eq2 eq4512
  have eq343 := Equation2_4512_implies_Equation343 G eq2 eq4512
  have eq411 := Equation2_4512_implies_Equation411 G eq2 eq4512
  have eq419 := Equation2_4512_implies_Equation419 G eq2 eq4512
  have eq429 := Equation2_4512_implies_Equation429 G eq2 eq4512
  have eq440 := Equation2_4512_implies_Equation440 G eq2 eq4512
  have eq477 := Equation2_4512_implies_Equation477 G eq2 eq4512
  have eq504 := Equation2_4512_implies_Equation504 G eq2 eq4512
  have eq513 := Equation2_4512_implies_Equation513 G eq2 eq4512
  have eq3253 := Equation2_4512_implies_Equation3253 G eq2 eq4512
  have eq3255 := Equation2_4512_implies_Equation3255 G eq2 eq4512
  have eq3256 := Equation2_4512_implies_Equation3256 G eq2 eq4512
  have eq3258 := Equation2_4512_implies_Equation3258 G eq2 eq4512
  have eq3259 := Equation2_4512_implies_Equation3259 G eq2 eq4512
  have eq3260 := Equation2_4512_implies_Equation3260 G eq2 eq4512
  have eq3261 := Equation2_4512_implies_Equation3261 G eq2 eq4512
  have eq3264 := Equation2_4512_implies_Equation3264 G eq2 eq4512
  have eq3265 := Equation2_4512_implies_Equation3265 G eq2 eq4512
  have eq3267 := Equation2_4512_implies_Equation3267 G eq2 eq4512
  have eq3271 := Equation2_4512_implies_Equation3271 G eq2 eq4512
  have eq3273 := Equation2_4512_implies_Equation3273 G eq2 eq4512
  have eq3274 := Equation2_4512_implies_Equation3274 G eq2 eq4512
  have eq3275 := Equation2_4512_implies_Equation3275 G eq2 eq4512
  have eq3277 := Equation2_4512_implies_Equation3277 G eq2 eq4512
  have eq3278 := Equation2_4512_implies_Equation3278 G eq2 eq4512
  have eq3290 := Equation2_4512_implies_Equation3290 G eq2 eq4512
  have eq3292 := Equation2_4512_implies_Equation3292 G eq2 eq4512
  have eq3300 := Equation2_4512_implies_Equation3300 G eq2 eq4512
  have eq3306 := Equation2_4512_implies_Equation3306 G eq2 eq4512
  have eq3308 := Equation2_4512_implies_Equation3308 G eq2 eq4512
  have eq3309 := Equation2_4512_implies_Equation3309 G eq2 eq4512
  have eq3315 := Equation2_4512_implies_Equation3315 G eq2 eq4512
  have eq3316 := Equation2_4512_implies_Equation3316 G eq2 eq4512
  have eq3319 := Equation2_4512_implies_Equation3319 G eq2 eq4512
  have eq3322 := Equation2_4512_implies_Equation3322 G eq2 eq4512
  have eq3323 := Equation2_4512_implies_Equation3323 G eq2 eq4512
  have eq3326 := Equation2_4512_implies_Equation3326 G eq2 eq4512
  have eq3331 := Equation2_4512_implies_Equation3331 G eq2 eq4512
  have eq3334 := Equation2_4512_implies_Equation3334 G eq2 eq4512
  have eq3342 := Equation2_4512_implies_Equation3342 G eq2 eq4512
  have eq3346 := Equation2_4512_implies_Equation3346 G eq2 eq4512
  have eq3350 := Equation2_4512_implies_Equation3350 G eq2 eq4512
  have eq3353 := Equation2_4512_implies_Equation3353 G eq2 eq4512
  have eq3388 := Equation2_4512_implies_Equation3388 G eq2 eq4512
  have eq3414 := Equation2_4512_implies_Equation3414 G eq2 eq4512
  have eq4268 := Equation2_4512_implies_Equation4268 G eq2 eq4512
  have eq4269 := Equation2_4512_implies_Equation4269 G eq2 eq4512
  have eq4270 := Equation2_4512_implies_Equation4270 G eq2 eq4512
  have eq4271 := Equation2_4512_implies_Equation4271 G eq2 eq4512
  have eq4272 := Equation2_4512_implies_Equation4272 G eq2 eq4512
  have eq4273 := Equation2_4512_implies_Equation4273 G eq2 eq4512
  have eq4274 := Equation2_4512_implies_Equation4274 G eq2 eq4512
  have eq4275 := Equation2_4512_implies_Equation4275 G eq2 eq4512
  have eq4276 := Equation2_4512_implies_Equation4276 G eq2 eq4512
  have eq4277 := Equation2_4512_implies_Equation4277 G eq2 eq4512
  have eq4278 := Equation2_4512_implies_Equation4278 G eq2 eq4512
  have eq4279 := Equation2_4512_implies_Equation4279 G eq2 eq4512
  have eq4280 := Equation2_4512_implies_Equation4280 G eq2 eq4512
  have eq4283 := Equation2_4512_implies_Equation4283 G eq2 eq4512
  have eq4284 := Equation2_4512_implies_Equation4284 G eq2 eq4512
  have eq4286 := Equation2_4512_implies_Equation4286 G eq2 eq4512
  have eq4287 := Equation2_4512_implies_Equation4287 G eq2 eq4512
  have eq4288 := Equation2_4512_implies_Equation4288 G eq2 eq4512
  have eq4290 := Equation2_4512_implies_Equation4290 G eq2 eq4512
  have eq4291 := Equation2_4512_implies_Equation4291 G eq2 eq4512
  have eq4293 := Equation2_4512_implies_Equation4293 G eq2 eq4512
  have eq4296 := Equation2_4512_implies_Equation4296 G eq2 eq4512
  have eq4297 := Equation2_4512_implies_Equation4297 G eq2 eq4512
  have eq4299 := Equation2_4512_implies_Equation4299 G eq2 eq4512
  have eq4300 := Equation2_4512_implies_Equation4300 G eq2 eq4512
  have eq4301 := Equation2_4512_implies_Equation4301 G eq2 eq4512
  have eq4304 := Equation2_4512_implies_Equation4304 G eq2 eq4512
  have eq4305 := Equation2_4512_implies_Equation4305 G eq2 eq4512
  have eq4314 := Equation2_4512_implies_Equation4314 G eq2 eq4512
  have eq4315 := Equation2_4512_implies_Equation4315 G eq2 eq4512
  have eq4318 := Equation2_4512_implies_Equation4318 G eq2 eq4512
  have eq4320 := Equation2_4512_implies_Equation4320 G eq2 eq4512
  have eq4321 := Equation2_4512_implies_Equation4321 G eq2 eq4512
  have eq4325 := Equation2_4512_implies_Equation4325 G eq2 eq4512
  have eq4327 := Equation2_4512_implies_Equation4327 G eq2 eq4512
  have eq4331 := Equation2_4512_implies_Equation4331 G eq2 eq4512
  have eq4343 := Equation2_4512_implies_Equation4343 G eq2 eq4512
  have eq4358 := Equation2_4512_implies_Equation4358 G eq2 eq4512
  have eq4362 := Equation2_4512_implies_Equation4362 G eq2 eq4512
  have eq4364 := Equation2_4512_implies_Equation4364 G eq2 eq4512
  have eq4369 := Equation2_4512_implies_Equation4369 G eq2 eq4512
  exact ⟨eq1, eq2, eq3, eq4, eq5, eq8, eq10, eq11, eq14, eq16, eq38, eq39, eq40, eq41, eq43, eq47, eq56, eq66, eq75, eq307, eq308, eq309, eq310, eq311, eq312, eq313, eq314, eq315, eq316, eq318, eq323, eq325, eq326, eq327, eq329, eq332, eq333, eq343, eq411, eq419, eq429, eq440, eq477, eq504, eq513, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq3322, eq3323, eq3326, eq3331, eq3334, eq3342, eq3346, eq3350, eq3353, eq3388, eq3414, eq4268, eq4269, eq4270, eq4271, eq4272, eq4273, eq4274, eq4275, eq4276, eq4277, eq4278, eq4279, eq4280, eq4283, eq4284, eq4286, eq4287, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4300, eq4301, eq4304, eq4305, eq4314, eq4315, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT2_implied_by_long (G : Type*) [Magma G] : AssociativeTheory2_long G -> AssociativeTheory2 G :=
fun ⟨_, h2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h2, h4512⟩

theorem AT2_equiv (G : Type*) [Magma G] : AssociativeTheory2 G <-> AssociativeTheory2_long G :=
Iff.intro (AT2_implies_long G) (AT2_implied_by_long G)

theorem AT3_implies_long (G : Type*) [Magma G] (h : AssociativeTheory3 G) : AssociativeTheory3_long G := by
  obtain ⟨eq3, eq4512⟩ := h
  have eq1 := Equation3_4512_implies_Equation1 G eq3 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  have eq307 := Equation3_4512_implies_Equation307 G eq3 eq4512
  have eq323 := Equation3_4512_implies_Equation323 G eq3 eq4512
  have eq326 := Equation3_4512_implies_Equation326 G eq3 eq4512
  have eq411 := Equation3_4512_implies_Equation411 G eq3 eq4512
  have eq3253 := Equation3_4512_implies_Equation3253 G eq3 eq4512
  have eq3306 := Equation3_4512_implies_Equation3306 G eq3 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3_4512_implies_Equation3316 G eq3 eq4512
  have eq3319 := Equation3_4512_implies_Equation3319 G eq3 eq4512
  have eq4284 := Equation3_4512_implies_Equation4284 G eq3 eq4512
  exact ⟨eq1, eq3, eq8, eq47, eq307, eq323, eq326, eq411, eq3253, eq3306, eq3309, eq3316, eq3319, eq4284, eq4512⟩

theorem AT3_implied_by_long (G : Type*) [Magma G] : AssociativeTheory3_long G -> AssociativeTheory3 G :=
fun ⟨_, h3, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h4512⟩

theorem AT3_equiv (G : Type*) [Magma G] : AssociativeTheory3 G <-> AssociativeTheory3_long G :=
Iff.intro (AT3_implies_long G) (AT3_implied_by_long G)

theorem AT4_implies_long (G : Type*) [Magma G] (h : AssociativeTheory4 G) : AssociativeTheory4_long G := by
  obtain ⟨eq4, eq4512⟩ := h
  have eq1 := Equation4_4512_implies_Equation1 G eq4 eq4512
  have eq3 := Equation4_4512_implies_Equation3 G eq4 eq4512
  have eq8 := Equation4_4512_implies_Equation8 G eq4 eq4512
  have eq10 := Equation4_4512_implies_Equation10 G eq4 eq4512
  have eq11 := Equation4_4512_implies_Equation11 G eq4 eq4512
  have eq38 := Equation4_4512_implies_Equation38 G eq4 eq4512
  have eq47 := Equation4_4512_implies_Equation47 G eq4 eq4512
  have eq56 := Equation4_4512_implies_Equation56 G eq4 eq4512
  have eq307 := Equation4_4512_implies_Equation307 G eq4 eq4512
  have eq308 := Equation4_4512_implies_Equation308 G eq4 eq4512
  have eq309 := Equation4_4512_implies_Equation309 G eq4 eq4512
  have eq310 := Equation4_4512_implies_Equation310 G eq4 eq4512
  have eq311 := Equation4_4512_implies_Equation311 G eq4 eq4512
  have eq323 := Equation4_4512_implies_Equation323 G eq4 eq4512
  have eq325 := Equation4_4512_implies_Equation325 G eq4 eq4512
  have eq326 := Equation4_4512_implies_Equation326 G eq4 eq4512
  have eq327 := Equation4_4512_implies_Equation327 G eq4 eq4512
  have eq329 := Equation4_4512_implies_Equation329 G eq4 eq4512
  have eq411 := Equation4_4512_implies_Equation411 G eq4 eq4512
  have eq419 := Equation4_4512_implies_Equation419 G eq4 eq4512
  have eq429 := Equation4_4512_implies_Equation429 G eq4 eq4512
  have eq440 := Equation4_4512_implies_Equation440 G eq4 eq4512
  have eq3253 := Equation4_4512_implies_Equation3253 G eq4 eq4512
  have eq3255 := Equation4_4512_implies_Equation3255 G eq4 eq4512
  have eq3256 := Equation4_4512_implies_Equation3256 G eq4 eq4512
  have eq3258 := Equation4_4512_implies_Equation3258 G eq4 eq4512
  have eq3259 := Equation4_4512_implies_Equation3259 G eq4 eq4512
  have eq3260 := Equation4_4512_implies_Equation3260 G eq4 eq4512
  have eq3261 := Equation4_4512_implies_Equation3261 G eq4 eq4512
  have eq3264 := Equation4_4512_implies_Equation3264 G eq4 eq4512
  have eq3265 := Equation4_4512_implies_Equation3265 G eq4 eq4512
  have eq3267 := Equation4_4512_implies_Equation3267 G eq4 eq4512
  have eq3306 := Equation4_4512_implies_Equation3306 G eq4 eq4512
  have eq3308 := Equation4_4512_implies_Equation3308 G eq4 eq4512
  have eq3309 := Equation4_4512_implies_Equation3309 G eq4 eq4512
  have eq3315 := Equation4_4512_implies_Equation3315 G eq4 eq4512
  have eq3316 := Equation4_4512_implies_Equation3316 G eq4 eq4512
  have eq3319 := Equation4_4512_implies_Equation3319 G eq4 eq4512
  have eq3322 := Equation4_4512_implies_Equation3322 G eq4 eq4512
  have eq3323 := Equation4_4512_implies_Equation3323 G eq4 eq4512
  have eq3326 := Equation4_4512_implies_Equation3326 G eq4 eq4512
  have eq3331 := Equation4_4512_implies_Equation3331 G eq4 eq4512
  have eq3334 := Equation4_4512_implies_Equation3334 G eq4 eq4512
  have eq4268 := Equation4_4512_implies_Equation4268 G eq4 eq4512
  have eq4269 := Equation4_4512_implies_Equation4269 G eq4 eq4512
  have eq4270 := Equation4_4512_implies_Equation4270 G eq4 eq4512
  have eq4271 := Equation4_4512_implies_Equation4271 G eq4 eq4512
  have eq4283 := Equation4_4512_implies_Equation4283 G eq4 eq4512
  have eq4284 := Equation4_4512_implies_Equation4284 G eq4 eq4512
  have eq4286 := Equation4_4512_implies_Equation4286 G eq4 eq4512
  have eq4287 := Equation4_4512_implies_Equation4287 G eq4 eq4512
  have eq4288 := Equation4_4512_implies_Equation4288 G eq4 eq4512
  have eq4314 := Equation4_4512_implies_Equation4314 G eq4 eq4512
  have eq4315 := Equation4_4512_implies_Equation4315 G eq4 eq4512
  have eq4318 := Equation4_4512_implies_Equation4318 G eq4 eq4512
  have eq4358 := Equation4_4512_implies_Equation4358 G eq4 eq4512
  exact ⟨eq1, eq3, eq4, eq8, eq10, eq11, eq38, eq47, eq56, eq307, eq308, eq309, eq310, eq311, eq323, eq325, eq326, eq327, eq329, eq411, eq419, eq429, eq440, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq3322, eq3323, eq3326, eq3331, eq3334, eq4268, eq4269, eq4270, eq4271, eq4283, eq4284, eq4286, eq4287, eq4288, eq4314, eq4315, eq4318, eq4358, eq4512⟩

theorem AT4_implied_by_long (G : Type*) [Magma G] : AssociativeTheory4_long G -> AssociativeTheory4 G :=
fun ⟨_, _, h4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4, h4512⟩

theorem AT4_equiv (G : Type*) [Magma G] : AssociativeTheory4 G <-> AssociativeTheory4_long G :=
Iff.intro (AT4_implies_long G) (AT4_implied_by_long G)

theorem AT5_implies_long (G : Type*) [Magma G] (h : AssociativeTheory5 G) : AssociativeTheory5_long G := by
  obtain ⟨eq5, eq4512⟩ := h
  have eq1 := Equation5_4512_implies_Equation1 G eq5 eq4512
  have eq3 := Equation5_4512_implies_Equation3 G eq5 eq4512
  have eq8 := Equation5_4512_implies_Equation8 G eq5 eq4512
  have eq10 := Equation5_4512_implies_Equation10 G eq5 eq4512
  have eq16 := Equation5_4512_implies_Equation16 G eq5 eq4512
  have eq39 := Equation5_4512_implies_Equation39 G eq5 eq4512
  have eq47 := Equation5_4512_implies_Equation47 G eq5 eq4512
  have eq75 := Equation5_4512_implies_Equation75 G eq5 eq4512
  have eq307 := Equation5_4512_implies_Equation307 G eq5 eq4512
  have eq309 := Equation5_4512_implies_Equation309 G eq5 eq4512
  have eq312 := Equation5_4512_implies_Equation312 G eq5 eq4512
  have eq315 := Equation5_4512_implies_Equation315 G eq5 eq4512
  have eq318 := Equation5_4512_implies_Equation318 G eq5 eq4512
  have eq323 := Equation5_4512_implies_Equation323 G eq5 eq4512
  have eq326 := Equation5_4512_implies_Equation326 G eq5 eq4512
  have eq329 := Equation5_4512_implies_Equation329 G eq5 eq4512
  have eq333 := Equation5_4512_implies_Equation333 G eq5 eq4512
  have eq343 := Equation5_4512_implies_Equation343 G eq5 eq4512
  have eq411 := Equation5_4512_implies_Equation411 G eq5 eq4512
  have eq419 := Equation5_4512_implies_Equation419 G eq5 eq4512
  have eq429 := Equation5_4512_implies_Equation429 G eq5 eq4512
  have eq513 := Equation5_4512_implies_Equation513 G eq5 eq4512
  have eq3253 := Equation5_4512_implies_Equation3253 G eq5 eq4512
  have eq3255 := Equation5_4512_implies_Equation3255 G eq5 eq4512
  have eq3258 := Equation5_4512_implies_Equation3258 G eq5 eq4512
  have eq3261 := Equation5_4512_implies_Equation3261 G eq5 eq4512
  have eq3264 := Equation5_4512_implies_Equation3264 G eq5 eq4512
  have eq3271 := Equation5_4512_implies_Equation3271 G eq5 eq4512
  have eq3274 := Equation5_4512_implies_Equation3274 G eq5 eq4512
  have eq3278 := Equation5_4512_implies_Equation3278 G eq5 eq4512
  have eq3292 := Equation5_4512_implies_Equation3292 G eq5 eq4512
  have eq3300 := Equation5_4512_implies_Equation3300 G eq5 eq4512
  have eq3306 := Equation5_4512_implies_Equation3306 G eq5 eq4512
  have eq3309 := Equation5_4512_implies_Equation3309 G eq5 eq4512
  have eq3316 := Equation5_4512_implies_Equation3316 G eq5 eq4512
  have eq3319 := Equation5_4512_implies_Equation3319 G eq5 eq4512
  have eq3322 := Equation5_4512_implies_Equation3322 G eq5 eq4512
  have eq3326 := Equation5_4512_implies_Equation3326 G eq5 eq4512
  have eq3334 := Equation5_4512_implies_Equation3334 G eq5 eq4512
  have eq3346 := Equation5_4512_implies_Equation3346 G eq5 eq4512
  have eq3353 := Equation5_4512_implies_Equation3353 G eq5 eq4512
  have eq3388 := Equation5_4512_implies_Equation3388 G eq5 eq4512
  have eq3414 := Equation5_4512_implies_Equation3414 G eq5 eq4512
  have eq4269 := Equation5_4512_implies_Equation4269 G eq5 eq4512
  have eq4272 := Equation5_4512_implies_Equation4272 G eq5 eq4512
  have eq4275 := Equation5_4512_implies_Equation4275 G eq5 eq4512
  have eq4278 := Equation5_4512_implies_Equation4278 G eq5 eq4512
  have eq4284 := Equation5_4512_implies_Equation4284 G eq5 eq4512
  have eq4287 := Equation5_4512_implies_Equation4287 G eq5 eq4512
  have eq4291 := Equation5_4512_implies_Equation4291 G eq5 eq4512
  have eq4296 := Equation5_4512_implies_Equation4296 G eq5 eq4512
  have eq4300 := Equation5_4512_implies_Equation4300 G eq5 eq4512
  have eq4304 := Equation5_4512_implies_Equation4304 G eq5 eq4512
  have eq4320 := Equation5_4512_implies_Equation4320 G eq5 eq4512
  have eq4327 := Equation5_4512_implies_Equation4327 G eq5 eq4512
  have eq4362 := Equation5_4512_implies_Equation4362 G eq5 eq4512
  exact ⟨eq1, eq3, eq5, eq8, eq10, eq16, eq39, eq47, eq75, eq307, eq309, eq312, eq315, eq318, eq323, eq326, eq329, eq333, eq343, eq411, eq419, eq429, eq513, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq3300, eq3306, eq3309, eq3316, eq3319, eq3322, eq3326, eq3334, eq3346, eq3353, eq3388, eq3414, eq4269, eq4272, eq4275, eq4278, eq4284, eq4287, eq4291, eq4296, eq4300, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT5_implied_by_long (G : Type*) [Magma G] : AssociativeTheory5_long G -> AssociativeTheory5 G :=
fun ⟨_, _, h5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h5, h4512⟩

theorem AT5_equiv (G : Type*) [Magma G] : AssociativeTheory5 G <-> AssociativeTheory5_long G :=
Iff.intro (AT5_implies_long G) (AT5_implied_by_long G)

theorem AT6_implies_long (G : Type*) [Magma G] (h : AssociativeTheory6 G) : AssociativeTheory6_long G := by
  obtain ⟨eq8, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq4512⟩

theorem AT6_implied_by_long (G : Type*) [Magma G] : AssociativeTheory6_long G -> AssociativeTheory6 G :=
fun ⟨_, h8, _, _, _, _, h4512⟩ => ⟨h8, h4512⟩

theorem AT6_equiv (G : Type*) [Magma G] : AssociativeTheory6 G <-> AssociativeTheory6_long G :=
Iff.intro (AT6_implies_long G) (AT6_implied_by_long G)

theorem AT7_implies_long (G : Type*) [Magma G] (h : AssociativeTheory7 G) : AssociativeTheory7_long G := by
  obtain ⟨eq10, eq4512⟩ := h
  have eq1 := Equation10_4512_implies_Equation1 G eq10 eq4512
  have eq3 := Equation10_4512_implies_Equation3 G eq10 eq4512
  have eq8 := Equation10_4512_implies_Equation8 G eq10 eq4512
  have eq47 := Equation10_4512_implies_Equation47 G eq10 eq4512
  have eq307 := Equation10_4512_implies_Equation307 G eq10 eq4512
  have eq309 := Equation10_4512_implies_Equation309 G eq10 eq4512
  have eq323 := Equation10_4512_implies_Equation323 G eq10 eq4512
  have eq326 := Equation10_4512_implies_Equation326 G eq10 eq4512
  have eq329 := Equation10_4512_implies_Equation329 G eq10 eq4512
  have eq411 := Equation10_4512_implies_Equation411 G eq10 eq4512
  have eq419 := Equation10_4512_implies_Equation419 G eq10 eq4512
  have eq429 := Equation10_4512_implies_Equation429 G eq10 eq4512
  have eq3253 := Equation10_4512_implies_Equation3253 G eq10 eq4512
  have eq3255 := Equation10_4512_implies_Equation3255 G eq10 eq4512
  have eq3258 := Equation10_4512_implies_Equation3258 G eq10 eq4512
  have eq3261 := Equation10_4512_implies_Equation3261 G eq10 eq4512
  have eq3264 := Equation10_4512_implies_Equation3264 G eq10 eq4512
  have eq3306 := Equation10_4512_implies_Equation3306 G eq10 eq4512
  have eq3309 := Equation10_4512_implies_Equation3309 G eq10 eq4512
  have eq3316 := Equation10_4512_implies_Equation3316 G eq10 eq4512
  have eq3319 := Equation10_4512_implies_Equation3319 G eq10 eq4512
  have eq3322 := Equation10_4512_implies_Equation3322 G eq10 eq4512
  have eq3326 := Equation10_4512_implies_Equation3326 G eq10 eq4512
  have eq3334 := Equation10_4512_implies_Equation3334 G eq10 eq4512
  have eq4269 := Equation10_4512_implies_Equation4269 G eq10 eq4512
  have eq4284 := Equation10_4512_implies_Equation4284 G eq10 eq4512
  have eq4287 := Equation10_4512_implies_Equation4287 G eq10 eq4512
  exact ⟨eq1, eq3, eq8, eq10, eq47, eq307, eq309, eq323, eq326, eq329, eq411, eq419, eq429, eq3253, eq3255, eq3258, eq3261, eq3264, eq3306, eq3309, eq3316, eq3319, eq3322, eq3326, eq3334, eq4269, eq4284, eq4287, eq4512⟩

theorem AT7_implied_by_long (G : Type*) [Magma G] : AssociativeTheory7_long G -> AssociativeTheory7 G :=
fun ⟨_, _, _, h10, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h10, h4512⟩

theorem AT7_equiv (G : Type*) [Magma G] : AssociativeTheory7 G <-> AssociativeTheory7_long G :=
Iff.intro (AT7_implies_long G) (AT7_implied_by_long G)

theorem AT8_implies_long (G : Type*) [Magma G] (h : AssociativeTheory8 G) : AssociativeTheory8_long G := by
  obtain ⟨eq11, eq4512⟩ := h
  have eq1 := Equation11_4512_implies_Equation1 G eq11 eq4512
  have eq8 := Equation11_4512_implies_Equation8 G eq11 eq4512
  have eq411 := Equation11_4512_implies_Equation411 G eq11 eq4512
  have eq419 := Equation11_4512_implies_Equation419 G eq11 eq4512
  have eq429 := Equation11_4512_implies_Equation429 G eq11 eq4512
  have eq440 := Equation11_4512_implies_Equation440 G eq11 eq4512
  have eq3253 := Equation11_4512_implies_Equation3253 G eq11 eq4512
  have eq3256 := Equation11_4512_implies_Equation3256 G eq11 eq4512
  have eq3259 := Equation11_4512_implies_Equation3259 G eq11 eq4512
  have eq3261 := Equation11_4512_implies_Equation3261 G eq11 eq4512
  have eq3306 := Equation11_4512_implies_Equation3306 G eq11 eq4512
  have eq3308 := Equation11_4512_implies_Equation3308 G eq11 eq4512
  have eq3315 := Equation11_4512_implies_Equation3315 G eq11 eq4512
  have eq3319 := Equation11_4512_implies_Equation3319 G eq11 eq4512
  have eq3323 := Equation11_4512_implies_Equation3323 G eq11 eq4512
  have eq3331 := Equation11_4512_implies_Equation3331 G eq11 eq4512
  have eq3334 := Equation11_4512_implies_Equation3334 G eq11 eq4512
  have eq4270 := Equation11_4512_implies_Equation4270 G eq11 eq4512
  have eq4283 := Equation11_4512_implies_Equation4283 G eq11 eq4512
  have eq4358 := Equation11_4512_implies_Equation4358 G eq11 eq4512
  exact ⟨eq1, eq8, eq11, eq411, eq419, eq429, eq440, eq3253, eq3256, eq3259, eq3261, eq3306, eq3308, eq3315, eq3319, eq3323, eq3331, eq3334, eq4270, eq4283, eq4358, eq4512⟩

theorem AT8_implied_by_long (G : Type*) [Magma G] : AssociativeTheory8_long G -> AssociativeTheory8 G :=
fun ⟨_, _, h11, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h11, h4512⟩

theorem AT8_equiv (G : Type*) [Magma G] : AssociativeTheory8 G <-> AssociativeTheory8_long G :=
Iff.intro (AT8_implies_long G) (AT8_implied_by_long G)

theorem AT9_implies_long (G : Type*) [Magma G] (h : AssociativeTheory9 G) : AssociativeTheory9_long G := by
  obtain ⟨eq14, eq4512⟩ := h
  have eq1 := Equation14_4512_implies_Equation1 G eq14 eq4512
  have eq8 := Equation14_4512_implies_Equation8 G eq14 eq4512
  have eq11 := Equation14_4512_implies_Equation11 G eq14 eq4512
  have eq16 := Equation14_4512_implies_Equation16 G eq14 eq4512
  have eq40 := Equation14_4512_implies_Equation40 G eq14 eq4512
  have eq43 := Equation14_4512_implies_Equation43 G eq14 eq4512
  have eq411 := Equation14_4512_implies_Equation411 G eq14 eq4512
  have eq419 := Equation14_4512_implies_Equation419 G eq14 eq4512
  have eq429 := Equation14_4512_implies_Equation429 G eq14 eq4512
  have eq440 := Equation14_4512_implies_Equation440 G eq14 eq4512
  have eq477 := Equation14_4512_implies_Equation477 G eq14 eq4512
  have eq504 := Equation14_4512_implies_Equation504 G eq14 eq4512
  have eq513 := Equation14_4512_implies_Equation513 G eq14 eq4512
  have eq3253 := Equation14_4512_implies_Equation3253 G eq14 eq4512
  have eq3256 := Equation14_4512_implies_Equation3256 G eq14 eq4512
  have eq3259 := Equation14_4512_implies_Equation3259 G eq14 eq4512
  have eq3261 := Equation14_4512_implies_Equation3261 G eq14 eq4512
  have eq3271 := Equation14_4512_implies_Equation3271 G eq14 eq4512
  have eq3278 := Equation14_4512_implies_Equation3278 G eq14 eq4512
  have eq3306 := Equation14_4512_implies_Equation3306 G eq14 eq4512
  have eq3308 := Equation14_4512_implies_Equation3308 G eq14 eq4512
  have eq3315 := Equation14_4512_implies_Equation3315 G eq14 eq4512
  have eq3319 := Equation14_4512_implies_Equation3319 G eq14 eq4512
  have eq3323 := Equation14_4512_implies_Equation3323 G eq14 eq4512
  have eq3331 := Equation14_4512_implies_Equation3331 G eq14 eq4512
  have eq3334 := Equation14_4512_implies_Equation3334 G eq14 eq4512
  have eq3342 := Equation14_4512_implies_Equation3342 G eq14 eq4512
  have eq3346 := Equation14_4512_implies_Equation3346 G eq14 eq4512
  have eq3350 := Equation14_4512_implies_Equation3350 G eq14 eq4512
  have eq3353 := Equation14_4512_implies_Equation3353 G eq14 eq4512
  have eq3388 := Equation14_4512_implies_Equation3388 G eq14 eq4512
  have eq3414 := Equation14_4512_implies_Equation3414 G eq14 eq4512
  have eq4270 := Equation14_4512_implies_Equation4270 G eq14 eq4512
  have eq4273 := Equation14_4512_implies_Equation4273 G eq14 eq4512
  have eq4275 := Equation14_4512_implies_Equation4275 G eq14 eq4512
  have eq4283 := Equation14_4512_implies_Equation4283 G eq14 eq4512
  have eq4290 := Equation14_4512_implies_Equation4290 G eq14 eq4512
  have eq4297 := Equation14_4512_implies_Equation4297 G eq14 eq4512
  have eq4305 := Equation14_4512_implies_Equation4305 G eq14 eq4512
  have eq4320 := Equation14_4512_implies_Equation4320 G eq14 eq4512
  have eq4325 := Equation14_4512_implies_Equation4325 G eq14 eq4512
  have eq4358 := Equation14_4512_implies_Equation4358 G eq14 eq4512
  have eq4362 := Equation14_4512_implies_Equation4362 G eq14 eq4512
  have eq4364 := Equation14_4512_implies_Equation4364 G eq14 eq4512
  have eq4369 := Equation14_4512_implies_Equation4369 G eq14 eq4512
  exact ⟨eq1, eq8, eq11, eq14, eq16, eq40, eq43, eq411, eq419, eq429, eq440, eq477, eq504, eq513, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq3306, eq3308, eq3315, eq3319, eq3323, eq3331, eq3334, eq3342, eq3346, eq3350, eq3353, eq3388, eq3414, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT9_implied_by_long (G : Type*) [Magma G] : AssociativeTheory9_long G -> AssociativeTheory9 G :=
fun ⟨_, _, _, h14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h14, h4512⟩

theorem AT9_equiv (G : Type*) [Magma G] : AssociativeTheory9 G <-> AssociativeTheory9_long G :=
Iff.intro (AT9_implies_long G) (AT9_implied_by_long G)

theorem AT10_implies_long (G : Type*) [Magma G] (h : AssociativeTheory10 G) : AssociativeTheory10_long G := by
  obtain ⟨eq16, eq4512⟩ := h
  have eq1 := Equation16_4512_implies_Equation1 G eq16 eq4512
  have eq8 := Equation16_4512_implies_Equation8 G eq16 eq4512
  have eq411 := Equation16_4512_implies_Equation411 G eq16 eq4512
  have eq419 := Equation16_4512_implies_Equation419 G eq16 eq4512
  have eq429 := Equation16_4512_implies_Equation429 G eq16 eq4512
  have eq513 := Equation16_4512_implies_Equation513 G eq16 eq4512
  have eq3253 := Equation16_4512_implies_Equation3253 G eq16 eq4512
  have eq3261 := Equation16_4512_implies_Equation3261 G eq16 eq4512
  have eq3271 := Equation16_4512_implies_Equation3271 G eq16 eq4512
  have eq3278 := Equation16_4512_implies_Equation3278 G eq16 eq4512
  have eq3306 := Equation16_4512_implies_Equation3306 G eq16 eq4512
  have eq3319 := Equation16_4512_implies_Equation3319 G eq16 eq4512
  have eq3334 := Equation16_4512_implies_Equation3334 G eq16 eq4512
  have eq3346 := Equation16_4512_implies_Equation3346 G eq16 eq4512
  have eq3353 := Equation16_4512_implies_Equation3353 G eq16 eq4512
  have eq3388 := Equation16_4512_implies_Equation3388 G eq16 eq4512
  have eq3414 := Equation16_4512_implies_Equation3414 G eq16 eq4512
  have eq4275 := Equation16_4512_implies_Equation4275 G eq16 eq4512
  have eq4320 := Equation16_4512_implies_Equation4320 G eq16 eq4512
  have eq4362 := Equation16_4512_implies_Equation4362 G eq16 eq4512
  exact ⟨eq1, eq8, eq16, eq411, eq419, eq429, eq513, eq3253, eq3261, eq3271, eq3278, eq3306, eq3319, eq3334, eq3346, eq3353, eq3388, eq3414, eq4275, eq4320, eq4362, eq4512⟩

theorem AT10_implied_by_long (G : Type*) [Magma G] : AssociativeTheory10_long G -> AssociativeTheory10 G :=
fun ⟨_, _, h16, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h16, h4512⟩

theorem AT10_equiv (G : Type*) [Magma G] : AssociativeTheory10 G <-> AssociativeTheory10_long G :=
Iff.intro (AT10_implies_long G) (AT10_implied_by_long G)

theorem AT11_implies_long (G : Type*) [Magma G] (h : AssociativeTheory11 G) : AssociativeTheory11_long G := by
  obtain ⟨eq38, eq4512⟩ := h
  have eq1 := Equation38_4512_implies_Equation1 G eq38 eq4512
  have eq307 := Equation38_4512_implies_Equation307 G eq38 eq4512
  have eq308 := Equation38_4512_implies_Equation308 G eq38 eq4512
  have eq309 := Equation38_4512_implies_Equation309 G eq38 eq4512
  have eq310 := Equation38_4512_implies_Equation310 G eq38 eq4512
  have eq311 := Equation38_4512_implies_Equation311 G eq38 eq4512
  have eq323 := Equation38_4512_implies_Equation323 G eq38 eq4512
  have eq325 := Equation38_4512_implies_Equation325 G eq38 eq4512
  have eq326 := Equation38_4512_implies_Equation326 G eq38 eq4512
  have eq327 := Equation38_4512_implies_Equation327 G eq38 eq4512
  have eq329 := Equation38_4512_implies_Equation329 G eq38 eq4512
  have eq3253 := Equation38_4512_implies_Equation3253 G eq38 eq4512
  have eq3255 := Equation38_4512_implies_Equation3255 G eq38 eq4512
  have eq3256 := Equation38_4512_implies_Equation3256 G eq38 eq4512
  have eq3258 := Equation38_4512_implies_Equation3258 G eq38 eq4512
  have eq3259 := Equation38_4512_implies_Equation3259 G eq38 eq4512
  have eq3260 := Equation38_4512_implies_Equation3260 G eq38 eq4512
  have eq3261 := Equation38_4512_implies_Equation3261 G eq38 eq4512
  have eq3264 := Equation38_4512_implies_Equation3264 G eq38 eq4512
  have eq3265 := Equation38_4512_implies_Equation3265 G eq38 eq4512
  have eq3267 := Equation38_4512_implies_Equation3267 G eq38 eq4512
  have eq3306 := Equation38_4512_implies_Equation3306 G eq38 eq4512
  have eq3308 := Equation38_4512_implies_Equation3308 G eq38 eq4512
  have eq3309 := Equation38_4512_implies_Equation3309 G eq38 eq4512
  have eq3315 := Equation38_4512_implies_Equation3315 G eq38 eq4512
  have eq3316 := Equation38_4512_implies_Equation3316 G eq38 eq4512
  have eq3319 := Equation38_4512_implies_Equation3319 G eq38 eq4512
  have eq3322 := Equation38_4512_implies_Equation3322 G eq38 eq4512
  have eq3323 := Equation38_4512_implies_Equation3323 G eq38 eq4512
  have eq3326 := Equation38_4512_implies_Equation3326 G eq38 eq4512
  have eq3331 := Equation38_4512_implies_Equation3331 G eq38 eq4512
  have eq3334 := Equation38_4512_implies_Equation3334 G eq38 eq4512
  have eq4268 := Equation38_4512_implies_Equation4268 G eq38 eq4512
  have eq4269 := Equation38_4512_implies_Equation4269 G eq38 eq4512
  have eq4270 := Equation38_4512_implies_Equation4270 G eq38 eq4512
  have eq4271 := Equation38_4512_implies_Equation4271 G eq38 eq4512
  have eq4283 := Equation38_4512_implies_Equation4283 G eq38 eq4512
  have eq4284 := Equation38_4512_implies_Equation4284 G eq38 eq4512
  have eq4286 := Equation38_4512_implies_Equation4286 G eq38 eq4512
  have eq4287 := Equation38_4512_implies_Equation4287 G eq38 eq4512
  have eq4288 := Equation38_4512_implies_Equation4288 G eq38 eq4512
  have eq4314 := Equation38_4512_implies_Equation4314 G eq38 eq4512
  have eq4315 := Equation38_4512_implies_Equation4315 G eq38 eq4512
  have eq4318 := Equation38_4512_implies_Equation4318 G eq38 eq4512
  have eq4358 := Equation38_4512_implies_Equation4358 G eq38 eq4512
  exact ⟨eq1, eq38, eq307, eq308, eq309, eq310, eq311, eq323, eq325, eq326, eq327, eq329, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq3322, eq3323, eq3326, eq3331, eq3334, eq4268, eq4269, eq4270, eq4271, eq4283, eq4284, eq4286, eq4287, eq4288, eq4314, eq4315, eq4318, eq4358, eq4512⟩

theorem AT11_implied_by_long (G : Type*) [Magma G] : AssociativeTheory11_long G -> AssociativeTheory11 G :=
fun ⟨_, h38, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h38, h4512⟩

theorem AT11_equiv (G : Type*) [Magma G] : AssociativeTheory11 G <-> AssociativeTheory11_long G :=
Iff.intro (AT11_implies_long G) (AT11_implied_by_long G)

theorem AT12_implies_long (G : Type*) [Magma G] (h : AssociativeTheory12 G) : AssociativeTheory12_long G := by
  obtain ⟨eq39, eq4512⟩ := h
  have eq1 := Equation39_4512_implies_Equation1 G eq39 eq4512
  have eq307 := Equation39_4512_implies_Equation307 G eq39 eq4512
  have eq309 := Equation39_4512_implies_Equation309 G eq39 eq4512
  have eq312 := Equation39_4512_implies_Equation312 G eq39 eq4512
  have eq315 := Equation39_4512_implies_Equation315 G eq39 eq4512
  have eq318 := Equation39_4512_implies_Equation318 G eq39 eq4512
  have eq323 := Equation39_4512_implies_Equation323 G eq39 eq4512
  have eq326 := Equation39_4512_implies_Equation326 G eq39 eq4512
  have eq329 := Equation39_4512_implies_Equation329 G eq39 eq4512
  have eq333 := Equation39_4512_implies_Equation333 G eq39 eq4512
  have eq343 := Equation39_4512_implies_Equation343 G eq39 eq4512
  have eq3253 := Equation39_4512_implies_Equation3253 G eq39 eq4512
  have eq3255 := Equation39_4512_implies_Equation3255 G eq39 eq4512
  have eq3258 := Equation39_4512_implies_Equation3258 G eq39 eq4512
  have eq3261 := Equation39_4512_implies_Equation3261 G eq39 eq4512
  have eq3264 := Equation39_4512_implies_Equation3264 G eq39 eq4512
  have eq3271 := Equation39_4512_implies_Equation3271 G eq39 eq4512
  have eq3274 := Equation39_4512_implies_Equation3274 G eq39 eq4512
  have eq3278 := Equation39_4512_implies_Equation3278 G eq39 eq4512
  have eq3292 := Equation39_4512_implies_Equation3292 G eq39 eq4512
  have eq3300 := Equation39_4512_implies_Equation3300 G eq39 eq4512
  have eq3306 := Equation39_4512_implies_Equation3306 G eq39 eq4512
  have eq3309 := Equation39_4512_implies_Equation3309 G eq39 eq4512
  have eq3316 := Equation39_4512_implies_Equation3316 G eq39 eq4512
  have eq3319 := Equation39_4512_implies_Equation3319 G eq39 eq4512
  have eq3322 := Equation39_4512_implies_Equation3322 G eq39 eq4512
  have eq3326 := Equation39_4512_implies_Equation3326 G eq39 eq4512
  have eq3334 := Equation39_4512_implies_Equation3334 G eq39 eq4512
  have eq3346 := Equation39_4512_implies_Equation3346 G eq39 eq4512
  have eq3353 := Equation39_4512_implies_Equation3353 G eq39 eq4512
  have eq3388 := Equation39_4512_implies_Equation3388 G eq39 eq4512
  have eq3414 := Equation39_4512_implies_Equation3414 G eq39 eq4512
  have eq4269 := Equation39_4512_implies_Equation4269 G eq39 eq4512
  have eq4272 := Equation39_4512_implies_Equation4272 G eq39 eq4512
  have eq4275 := Equation39_4512_implies_Equation4275 G eq39 eq4512
  have eq4278 := Equation39_4512_implies_Equation4278 G eq39 eq4512
  have eq4284 := Equation39_4512_implies_Equation4284 G eq39 eq4512
  have eq4287 := Equation39_4512_implies_Equation4287 G eq39 eq4512
  have eq4291 := Equation39_4512_implies_Equation4291 G eq39 eq4512
  have eq4296 := Equation39_4512_implies_Equation4296 G eq39 eq4512
  have eq4300 := Equation39_4512_implies_Equation4300 G eq39 eq4512
  have eq4304 := Equation39_4512_implies_Equation4304 G eq39 eq4512
  have eq4320 := Equation39_4512_implies_Equation4320 G eq39 eq4512
  have eq4327 := Equation39_4512_implies_Equation4327 G eq39 eq4512
  have eq4362 := Equation39_4512_implies_Equation4362 G eq39 eq4512
  exact ⟨eq1, eq39, eq307, eq309, eq312, eq315, eq318, eq323, eq326, eq329, eq333, eq343, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq3300, eq3306, eq3309, eq3316, eq3319, eq3322, eq3326, eq3334, eq3346, eq3353, eq3388, eq3414, eq4269, eq4272, eq4275, eq4278, eq4284, eq4287, eq4291, eq4296, eq4300, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT12_implied_by_long (G : Type*) [Magma G] : AssociativeTheory12_long G -> AssociativeTheory12 G :=
fun ⟨_, h39, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h39, h4512⟩

theorem AT12_equiv (G : Type*) [Magma G] : AssociativeTheory12 G <-> AssociativeTheory12_long G :=
Iff.intro (AT12_implies_long G) (AT12_implied_by_long G)

theorem AT13_implies_long (G : Type*) [Magma G] (h : AssociativeTheory13 G) : AssociativeTheory13_long G := by
  obtain ⟨eq38, eq39, eq4512⟩ := h
  have eq41 := Equation38_39_4512_implies_Equation41 G eq38 eq39 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq40 := Equation41_4512_implies_Equation40 G eq41 eq4512
  have eq43 := Equation41_4512_implies_Equation43 G eq41 eq4512
  have eq307 := Equation41_4512_implies_Equation307 G eq41 eq4512
  have eq308 := Equation41_4512_implies_Equation308 G eq41 eq4512
  have eq309 := Equation41_4512_implies_Equation309 G eq41 eq4512
  have eq310 := Equation41_4512_implies_Equation310 G eq41 eq4512
  have eq311 := Equation41_4512_implies_Equation311 G eq41 eq4512
  have eq312 := Equation41_4512_implies_Equation312 G eq41 eq4512
  have eq313 := Equation41_4512_implies_Equation313 G eq41 eq4512
  have eq314 := Equation41_4512_implies_Equation314 G eq41 eq4512
  have eq315 := Equation41_4512_implies_Equation315 G eq41 eq4512
  have eq316 := Equation41_4512_implies_Equation316 G eq41 eq4512
  have eq318 := Equation41_4512_implies_Equation318 G eq41 eq4512
  have eq323 := Equation41_4512_implies_Equation323 G eq41 eq4512
  have eq325 := Equation41_4512_implies_Equation325 G eq41 eq4512
  have eq326 := Equation41_4512_implies_Equation326 G eq41 eq4512
  have eq327 := Equation41_4512_implies_Equation327 G eq41 eq4512
  have eq329 := Equation41_4512_implies_Equation329 G eq41 eq4512
  have eq332 := Equation41_4512_implies_Equation332 G eq41 eq4512
  have eq333 := Equation41_4512_implies_Equation333 G eq41 eq4512
  have eq343 := Equation41_4512_implies_Equation343 G eq41 eq4512
  have eq3253 := Equation41_4512_implies_Equation3253 G eq41 eq4512
  have eq3255 := Equation41_4512_implies_Equation3255 G eq41 eq4512
  have eq3256 := Equation41_4512_implies_Equation3256 G eq41 eq4512
  have eq3258 := Equation41_4512_implies_Equation3258 G eq41 eq4512
  have eq3259 := Equation41_4512_implies_Equation3259 G eq41 eq4512
  have eq3260 := Equation41_4512_implies_Equation3260 G eq41 eq4512
  have eq3261 := Equation41_4512_implies_Equation3261 G eq41 eq4512
  have eq3264 := Equation41_4512_implies_Equation3264 G eq41 eq4512
  have eq3265 := Equation41_4512_implies_Equation3265 G eq41 eq4512
  have eq3267 := Equation41_4512_implies_Equation3267 G eq41 eq4512
  have eq3271 := Equation41_4512_implies_Equation3271 G eq41 eq4512
  have eq3273 := Equation41_4512_implies_Equation3273 G eq41 eq4512
  have eq3274 := Equation41_4512_implies_Equation3274 G eq41 eq4512
  have eq3275 := Equation41_4512_implies_Equation3275 G eq41 eq4512
  have eq3277 := Equation41_4512_implies_Equation3277 G eq41 eq4512
  have eq3278 := Equation41_4512_implies_Equation3278 G eq41 eq4512
  have eq3290 := Equation41_4512_implies_Equation3290 G eq41 eq4512
  have eq3292 := Equation41_4512_implies_Equation3292 G eq41 eq4512
  have eq3300 := Equation41_4512_implies_Equation3300 G eq41 eq4512
  have eq3306 := Equation41_4512_implies_Equation3306 G eq41 eq4512
  have eq3308 := Equation41_4512_implies_Equation3308 G eq41 eq4512
  have eq3309 := Equation41_4512_implies_Equation3309 G eq41 eq4512
  have eq3315 := Equation41_4512_implies_Equation3315 G eq41 eq4512
  have eq3316 := Equation41_4512_implies_Equation3316 G eq41 eq4512
  have eq3319 := Equation41_4512_implies_Equation3319 G eq41 eq4512
  have eq3322 := Equation41_4512_implies_Equation3322 G eq41 eq4512
  have eq3323 := Equation41_4512_implies_Equation3323 G eq41 eq4512
  have eq3326 := Equation41_4512_implies_Equation3326 G eq41 eq4512
  have eq3331 := Equation41_4512_implies_Equation3331 G eq41 eq4512
  have eq3334 := Equation41_4512_implies_Equation3334 G eq41 eq4512
  have eq3342 := Equation41_4512_implies_Equation3342 G eq41 eq4512
  have eq3346 := Equation41_4512_implies_Equation3346 G eq41 eq4512
  have eq3350 := Equation41_4512_implies_Equation3350 G eq41 eq4512
  have eq3353 := Equation41_4512_implies_Equation3353 G eq41 eq4512
  have eq3388 := Equation41_4512_implies_Equation3388 G eq41 eq4512
  have eq3414 := Equation41_4512_implies_Equation3414 G eq41 eq4512
  have eq4268 := Equation41_4512_implies_Equation4268 G eq41 eq4512
  have eq4269 := Equation41_4512_implies_Equation4269 G eq41 eq4512
  have eq4270 := Equation41_4512_implies_Equation4270 G eq41 eq4512
  have eq4271 := Equation41_4512_implies_Equation4271 G eq41 eq4512
  have eq4272 := Equation41_4512_implies_Equation4272 G eq41 eq4512
  have eq4273 := Equation41_4512_implies_Equation4273 G eq41 eq4512
  have eq4274 := Equation41_4512_implies_Equation4274 G eq41 eq4512
  have eq4275 := Equation41_4512_implies_Equation4275 G eq41 eq4512
  have eq4276 := Equation41_4512_implies_Equation4276 G eq41 eq4512
  have eq4277 := Equation41_4512_implies_Equation4277 G eq41 eq4512
  have eq4278 := Equation41_4512_implies_Equation4278 G eq41 eq4512
  have eq4279 := Equation41_4512_implies_Equation4279 G eq41 eq4512
  have eq4280 := Equation41_4512_implies_Equation4280 G eq41 eq4512
  have eq4283 := Equation41_4512_implies_Equation4283 G eq41 eq4512
  have eq4284 := Equation41_4512_implies_Equation4284 G eq41 eq4512
  have eq4286 := Equation41_4512_implies_Equation4286 G eq41 eq4512
  have eq4287 := Equation41_4512_implies_Equation4287 G eq41 eq4512
  have eq4288 := Equation41_4512_implies_Equation4288 G eq41 eq4512
  have eq4290 := Equation41_4512_implies_Equation4290 G eq41 eq4512
  have eq4291 := Equation41_4512_implies_Equation4291 G eq41 eq4512
  have eq4293 := Equation41_4512_implies_Equation4293 G eq41 eq4512
  have eq4296 := Equation41_4512_implies_Equation4296 G eq41 eq4512
  have eq4297 := Equation41_4512_implies_Equation4297 G eq41 eq4512
  have eq4299 := Equation41_4512_implies_Equation4299 G eq41 eq4512
  have eq4300 := Equation41_4512_implies_Equation4300 G eq41 eq4512
  have eq4301 := Equation41_4512_implies_Equation4301 G eq41 eq4512
  have eq4304 := Equation41_4512_implies_Equation4304 G eq41 eq4512
  have eq4305 := Equation41_4512_implies_Equation4305 G eq41 eq4512
  have eq4314 := Equation41_4512_implies_Equation4314 G eq41 eq4512
  have eq4315 := Equation41_4512_implies_Equation4315 G eq41 eq4512
  have eq4318 := Equation41_4512_implies_Equation4318 G eq41 eq4512
  have eq4320 := Equation41_4512_implies_Equation4320 G eq41 eq4512
  have eq4321 := Equation41_4512_implies_Equation4321 G eq41 eq4512
  have eq4325 := Equation41_4512_implies_Equation4325 G eq41 eq4512
  have eq4327 := Equation41_4512_implies_Equation4327 G eq41 eq4512
  have eq4331 := Equation41_4512_implies_Equation4331 G eq41 eq4512
  have eq4343 := Equation41_4512_implies_Equation4343 G eq41 eq4512
  have eq4358 := Equation41_4512_implies_Equation4358 G eq41 eq4512
  have eq4362 := Equation41_4512_implies_Equation4362 G eq41 eq4512
  have eq4364 := Equation41_4512_implies_Equation4364 G eq41 eq4512
  have eq4369 := Equation41_4512_implies_Equation4369 G eq41 eq4512
  exact ⟨eq1, eq38, eq39, eq40, eq41, eq43, eq307, eq308, eq309, eq310, eq311, eq312, eq313, eq314, eq315, eq316, eq318, eq323, eq325, eq326, eq327, eq329, eq332, eq333, eq343, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq3322, eq3323, eq3326, eq3331, eq3334, eq3342, eq3346, eq3350, eq3353, eq3388, eq3414, eq4268, eq4269, eq4270, eq4271, eq4272, eq4273, eq4274, eq4275, eq4276, eq4277, eq4278, eq4279, eq4280, eq4283, eq4284, eq4286, eq4287, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4300, eq4301, eq4304, eq4305, eq4314, eq4315, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT13_implied_by_long (G : Type*) [Magma G] : AssociativeTheory13_long G -> AssociativeTheory13 G :=
fun ⟨_, h38, h39, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h38, h39, h4512⟩

theorem AT13_equiv (G : Type*) [Magma G] : AssociativeTheory13 G <-> AssociativeTheory13_long G :=
Iff.intro (AT13_implies_long G) (AT13_implied_by_long G)

theorem AT14_implies_long (G : Type*) [Magma G] (h : AssociativeTheory14 G) : AssociativeTheory14_long G := by
  obtain ⟨eq40, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4275, eq4290, eq4297, eq4512⟩

theorem AT14_implied_by_long (G : Type*) [Magma G] : AssociativeTheory14_long G -> AssociativeTheory14 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h4512⟩

theorem AT14_equiv (G : Type*) [Magma G] : AssociativeTheory14 G <-> AssociativeTheory14_long G :=
Iff.intro (AT14_implies_long G) (AT14_implied_by_long G)

theorem AT15_implies_long (G : Type*) [Magma G] (h : AssociativeTheory15 G) : AssociativeTheory15_long G := by
  obtain ⟨eq43, eq4512⟩ := h
  have eq1 := Equation43_4512_implies_Equation1 G eq43 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact ⟨eq1, eq43, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT15_implied_by_long (G : Type*) [Magma G] : AssociativeTheory15_long G -> AssociativeTheory15 G :=
fun ⟨_, h43, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4512⟩

theorem AT15_equiv (G : Type*) [Magma G] : AssociativeTheory15 G <-> AssociativeTheory15_long G :=
Iff.intro (AT15_implies_long G) (AT15_implied_by_long G)

theorem AT16_implies_long (G : Type*) [Magma G] (h : AssociativeTheory16 G) : AssociativeTheory16_long G := by
  obtain ⟨eq3, eq43, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  have eq307 := Equation3_4512_implies_Equation307 G eq3 eq4512
  have eq323 := Equation3_4512_implies_Equation323 G eq3 eq4512
  have eq326 := Equation3_4512_implies_Equation326 G eq3 eq4512
  have eq411 := Equation3_4512_implies_Equation411 G eq3 eq4512
  have eq3253 := Equation3_4512_implies_Equation3253 G eq3 eq4512
  have eq3306 := Equation3_4512_implies_Equation3306 G eq3 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3_4512_implies_Equation3316 G eq3 eq4512
  have eq3319 := Equation3_4512_implies_Equation3319 G eq3 eq4512
  have eq4284 := Equation3_4512_implies_Equation4284 G eq3 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq332 := Equation43_323_4512_implies_Equation332 G eq43 eq323 eq4512
  have eq3342 := Equation43_3306_4512_implies_Equation3342 G eq43 eq3306 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq333 := Equation323_4291_4512_implies_Equation333 G eq323 eq4291 eq4512
  have eq4321 := Equation323_4343_4512_implies_Equation4321 G eq323 eq4343 eq4512
  have eq325 := Equation326_4314_4512_implies_Equation325 G eq326 eq4314 eq4512
  have eq3315 := Equation332_4512_implies_Equation3315 G eq332 eq4512
  have eq3353 := Equation332_4512_implies_Equation3353 G eq332 eq4512
  exact ⟨eq1, eq3, eq8, eq43, eq47, eq307, eq323, eq325, eq326, eq332, eq333, eq411, eq3253, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq3342, eq3346, eq3353, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT16_implied_by_long (G : Type*) [Magma G] : AssociativeTheory16_long G -> AssociativeTheory16 G :=
fun ⟨_, h3, _, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h43, h4512⟩

theorem AT16_equiv (G : Type*) [Magma G] : AssociativeTheory16 G <-> AssociativeTheory16_long G :=
Iff.intro (AT16_implies_long G) (AT16_implied_by_long G)

theorem AT17_implies_long (G : Type*) [Magma G] (h : AssociativeTheory17 G) : AssociativeTheory17_long G := by
  obtain ⟨eq8, eq43, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq3342 := Equation43_3306_4512_implies_Equation3342 G eq43 eq3306 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq3315 := Equation3342_4512_implies_Equation3315 G eq3342 eq4512
  have eq3353 := Equation3342_4512_implies_Equation3353 G eq3342 eq4512
  exact ⟨eq1, eq8, eq43, eq411, eq3253, eq3306, eq3308, eq3315, eq3319, eq3342, eq3346, eq3353, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT17_implied_by_long (G : Type*) [Magma G] : AssociativeTheory17_long G -> AssociativeTheory17 G :=
fun ⟨_, h8, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h8, h43, h4512⟩

theorem AT17_equiv (G : Type*) [Magma G] : AssociativeTheory17 G <-> AssociativeTheory17_long G :=
Iff.intro (AT17_implies_long G) (AT17_implied_by_long G)

theorem AT18_implies_long (G : Type*) [Magma G] (h : AssociativeTheory18 G) : AssociativeTheory18_long G := by
  obtain ⟨eq40, eq43, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq40, eq43, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT18_implied_by_long (G : Type*) [Magma G] : AssociativeTheory18_long G -> AssociativeTheory18 G :=
fun ⟨_, h40, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h43, h4512⟩

theorem AT18_equiv (G : Type*) [Magma G] : AssociativeTheory18 G <-> AssociativeTheory18_long G :=
Iff.intro (AT18_implies_long G) (AT18_implied_by_long G)

theorem AT19_implies_long (G : Type*) [Magma G] (h : AssociativeTheory19 G) : AssociativeTheory19_long G := by
  obtain ⟨eq47, eq4512⟩ := h
  have eq1 := Equation47_4512_implies_Equation1 G eq47 eq4512
  exact ⟨eq1, eq47, eq4512⟩

theorem AT19_implied_by_long (G : Type*) [Magma G] : AssociativeTheory19_long G -> AssociativeTheory19 G :=
fun ⟨_, h47, h4512⟩ => ⟨h47, h4512⟩

theorem AT19_equiv (G : Type*) [Magma G] : AssociativeTheory19 G <-> AssociativeTheory19_long G :=
Iff.intro (AT19_implies_long G) (AT19_implied_by_long G)

theorem AT20_implies_long (G : Type*) [Magma G] (h : AssociativeTheory20 G) : AssociativeTheory20_long G := by
  obtain ⟨eq43, eq47, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact ⟨eq1, eq43, eq47, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT20_implied_by_long (G : Type*) [Magma G] : AssociativeTheory20_long G -> AssociativeTheory20 G :=
fun ⟨_, h43, h47, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h47, h4512⟩

theorem AT20_equiv (G : Type*) [Magma G] : AssociativeTheory20 G <-> AssociativeTheory20_long G :=
Iff.intro (AT20_implies_long G) (AT20_implied_by_long G)

theorem AT21_implies_long (G : Type*) [Magma G] (h : AssociativeTheory21 G) : AssociativeTheory21_long G := by
  obtain ⟨eq56, eq4512⟩ := h
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact ⟨eq1, eq47, eq56, eq4512⟩

theorem AT21_implied_by_long (G : Type*) [Magma G] : AssociativeTheory21_long G -> AssociativeTheory21 G :=
fun ⟨_, _, h56, h4512⟩ => ⟨h56, h4512⟩

theorem AT21_equiv (G : Type*) [Magma G] : AssociativeTheory21 G <-> AssociativeTheory21_long G :=
Iff.intro (AT21_implies_long G) (AT21_implied_by_long G)

theorem AT22_implies_long (G : Type*) [Magma G] (h : AssociativeTheory22 G) : AssociativeTheory22_long G := by
  obtain ⟨eq43, eq56, eq4512⟩ := h
  have eq66 := Equation43_56_4512_implies_Equation66 G eq43 eq56 eq4512
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  have eq75 := Equation66_4512_implies_Equation75 G eq66 eq4512
  have eq4276 := Equation66_4512_implies_Equation4276 G eq66 eq4512
  have eq4283 := Equation66_4512_implies_Equation4283 G eq66 eq4512
  have eq4290 := Equation66_4512_implies_Equation4290 G eq66 eq4512
  have eq4320 := Equation66_4512_implies_Equation4320 G eq66 eq4512
  have eq4358 := Equation66_4512_implies_Equation4358 G eq66 eq4512
  have eq4362 := Equation66_4512_implies_Equation4362 G eq66 eq4512
  have eq4364 := Equation66_4512_implies_Equation4364 G eq66 eq4512
  have eq4369 := Equation66_4512_implies_Equation4369 G eq66 eq4512
  exact ⟨eq1, eq43, eq47, eq56, eq66, eq75, eq4276, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT22_implied_by_long (G : Type*) [Magma G] : AssociativeTheory22_long G -> AssociativeTheory22 G :=
fun ⟨_, h43, _, h56, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h56, h4512⟩

theorem AT22_equiv (G : Type*) [Magma G] : AssociativeTheory22 G <-> AssociativeTheory22_long G :=
Iff.intro (AT22_implies_long G) (AT22_implied_by_long G)

theorem AT23_implies_long (G : Type*) [Magma G] (h : AssociativeTheory23 G) : AssociativeTheory23_long G := by
  obtain ⟨eq75, eq4512⟩ := h
  have eq1 := Equation75_4512_implies_Equation1 G eq75 eq4512
  have eq47 := Equation75_4512_implies_Equation47 G eq75 eq4512
  exact ⟨eq1, eq47, eq75, eq4512⟩

theorem AT23_implied_by_long (G : Type*) [Magma G] : AssociativeTheory23_long G -> AssociativeTheory23 G :=
fun ⟨_, _, h75, h4512⟩ => ⟨h75, h4512⟩

theorem AT23_equiv (G : Type*) [Magma G] : AssociativeTheory23 G <-> AssociativeTheory23_long G :=
Iff.intro (AT23_implies_long G) (AT23_implied_by_long G)

theorem AT24_implies_long (G : Type*) [Magma G] (h : AssociativeTheory24 G) : AssociativeTheory24_long G := by
  obtain ⟨eq56, eq75, eq4512⟩ := h
  have eq4276 := Equation56_75_4512_implies_Equation4276 G eq56 eq75 eq4512
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact ⟨eq1, eq47, eq56, eq75, eq4276, eq4512⟩

theorem AT24_implied_by_long (G : Type*) [Magma G] : AssociativeTheory24_long G -> AssociativeTheory24 G :=
fun ⟨_, _, h56, h75, _, h4512⟩ => ⟨h56, h75, h4512⟩

theorem AT24_equiv (G : Type*) [Magma G] : AssociativeTheory24 G <-> AssociativeTheory24_long G :=
Iff.intro (AT24_implies_long G) (AT24_implied_by_long G)

theorem AT25_implies_long (G : Type*) [Magma G] (h : AssociativeTheory25 G) : AssociativeTheory25_long G := by
  obtain ⟨eq307, eq4512⟩ := h
  have eq1 := Equation307_4512_implies_Equation1 G eq307 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4512⟩

theorem AT25_implied_by_long (G : Type*) [Magma G] : AssociativeTheory25_long G -> AssociativeTheory25 G :=
fun ⟨_, h307, _, h4512⟩ => ⟨h307, h4512⟩

theorem AT25_equiv (G : Type*) [Magma G] : AssociativeTheory25 G <-> AssociativeTheory25_long G :=
Iff.intro (AT25_implies_long G) (AT25_implied_by_long G)

theorem AT26_implies_long (G : Type*) [Magma G] (h : AssociativeTheory26 G) : AssociativeTheory26_long G := by
  obtain ⟨eq40, eq307, eq4512⟩ := h
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq308 := Equation316_4512_implies_Equation308 G eq316 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq312 := Equation316_4512_implies_Equation312 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq3258 := Equation316_4512_implies_Equation3258 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4284 := Equation316_4512_implies_Equation4284 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3271, eq3278, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT26_implied_by_long (G : Type*) [Magma G] : AssociativeTheory26_long G -> AssociativeTheory26 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h307, h4512⟩

theorem AT26_equiv (G : Type*) [Magma G] : AssociativeTheory26 G <-> AssociativeTheory26_long G :=
Iff.intro (AT26_implies_long G) (AT26_implied_by_long G)

theorem AT27_implies_long (G : Type*) [Magma G] (h : AssociativeTheory27 G) : AssociativeTheory27_long G := by
  obtain ⟨eq43, eq307, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact ⟨eq1, eq43, eq307, eq3253, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT27_implied_by_long (G : Type*) [Magma G] : AssociativeTheory27_long G -> AssociativeTheory27 G :=
fun ⟨_, h43, h307, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h307, h4512⟩

theorem AT27_equiv (G : Type*) [Magma G] : AssociativeTheory27 G <-> AssociativeTheory27_long G :=
Iff.intro (AT27_implies_long G) (AT27_implied_by_long G)

theorem AT28_implies_long (G : Type*) [Magma G] (h : AssociativeTheory28 G) : AssociativeTheory28_long G := by
  obtain ⟨eq40, eq43, eq307, eq4512⟩ := h
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq3264 := Equation308_4369_4512_implies_Equation3264 G eq308 eq4369 eq4512
  have eq3265 := Equation308_4369_4512_implies_Equation3265 G eq308 eq4369 eq4512
  have eq3260 := Equation308_4369_4512_implies_Equation3260 G eq308 eq4369 eq4512
  have eq309 := Equation3258_4320_4512_implies_Equation309 G eq3258 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq40, eq43, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT28_implied_by_long (G : Type*) [Magma G] : AssociativeTheory28_long G -> AssociativeTheory28 G :=
fun ⟨_, h40, h43, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h43, h307, h4512⟩

theorem AT28_equiv (G : Type*) [Magma G] : AssociativeTheory28 G <-> AssociativeTheory28_long G :=
Iff.intro (AT28_implies_long G) (AT28_implied_by_long G)

theorem AT29_implies_long (G : Type*) [Magma G] (h : AssociativeTheory29 G) : AssociativeTheory29_long G := by
  obtain ⟨eq308, eq4512⟩ := h
  have eq1 := Equation308_4512_implies_Equation1 G eq308 eq4512
  have eq307 := Equation308_4512_implies_Equation307 G eq308 eq4512
  have eq3253 := Equation308_4512_implies_Equation3253 G eq308 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  exact ⟨eq1, eq307, eq308, eq3253, eq3255, eq3256, eq4268, eq4512⟩

theorem AT29_implied_by_long (G : Type*) [Magma G] : AssociativeTheory29_long G -> AssociativeTheory29 G :=
fun ⟨_, _, h308, _, _, _, _, h4512⟩ => ⟨h308, h4512⟩

theorem AT29_equiv (G : Type*) [Magma G] : AssociativeTheory29 G <-> AssociativeTheory29_long G :=
Iff.intro (AT29_implies_long G) (AT29_implied_by_long G)

theorem AT30_implies_long (G : Type*) [Magma G] (h : AssociativeTheory30 G) : AssociativeTheory30_long G := by
  obtain ⟨eq309, eq4512⟩ := h
  have eq1 := Equation309_4512_implies_Equation1 G eq309 eq4512
  have eq307 := Equation309_4512_implies_Equation307 G eq309 eq4512
  have eq3253 := Equation309_4512_implies_Equation3253 G eq309 eq4512
  have eq3255 := Equation309_4512_implies_Equation3255 G eq309 eq4512
  have eq3258 := Equation309_4512_implies_Equation3258 G eq309 eq4512
  have eq3261 := Equation309_4512_implies_Equation3261 G eq309 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4284 := Equation309_4512_implies_Equation4284 G eq309 eq4512
  exact ⟨eq1, eq307, eq309, eq3253, eq3255, eq3258, eq3261, eq3264, eq4269, eq4284, eq4512⟩

theorem AT30_implied_by_long (G : Type*) [Magma G] : AssociativeTheory30_long G -> AssociativeTheory30 G :=
fun ⟨_, _, h309, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h4512⟩

theorem AT30_equiv (G : Type*) [Magma G] : AssociativeTheory30 G <-> AssociativeTheory30_long G :=
Iff.intro (AT30_implies_long G) (AT30_implied_by_long G)

theorem AT31_implies_long (G : Type*) [Magma G] (h : AssociativeTheory31 G) : AssociativeTheory31_long G := by
  obtain ⟨eq40, eq309, eq4512⟩ := h
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation313_4512_implies_Equation307 G eq313 eq4512
  have eq308 := Equation313_4512_implies_Equation308 G eq313 eq4512
  have eq310 := Equation313_4512_implies_Equation310 G eq313 eq4512
  have eq312 := Equation313_4512_implies_Equation312 G eq313 eq4512
  have eq315 := Equation313_4512_implies_Equation315 G eq313 eq4512
  have eq316 := Equation313_4512_implies_Equation316 G eq313 eq4512
  have eq3255 := Equation313_4512_implies_Equation3255 G eq313 eq4512
  have eq3258 := Equation313_4512_implies_Equation3258 G eq313 eq4512
  have eq3260 := Equation313_4512_implies_Equation3260 G eq313 eq4512
  have eq3264 := Equation313_4512_implies_Equation3264 G eq313 eq4512
  have eq3265 := Equation313_4512_implies_Equation3265 G eq313 eq4512
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3274 := Equation313_4512_implies_Equation3274 G eq313 eq4512
  have eq3275 := Equation313_4512_implies_Equation3275 G eq313 eq4512
  have eq3290 := Equation313_4512_implies_Equation3290 G eq313 eq4512
  have eq3292 := Equation313_4512_implies_Equation3292 G eq313 eq4512
  have eq4268 := Equation313_4512_implies_Equation4268 G eq313 eq4512
  have eq4269 := Equation313_4512_implies_Equation4269 G eq313 eq4512
  have eq4272 := Equation313_4512_implies_Equation4272 G eq313 eq4512
  have eq4273 := Equation313_4512_implies_Equation4273 G eq313 eq4512
  have eq4276 := Equation313_4512_implies_Equation4276 G eq313 eq4512
  have eq4277 := Equation313_4512_implies_Equation4277 G eq313 eq4512
  have eq4279 := Equation313_4512_implies_Equation4279 G eq313 eq4512
  have eq4280 := Equation313_4512_implies_Equation4280 G eq313 eq4512
  have eq4283 := Equation313_4512_implies_Equation4283 G eq313 eq4512
  have eq4284 := Equation313_4512_implies_Equation4284 G eq313 eq4512
  have eq4286 := Equation313_4512_implies_Equation4286 G eq313 eq4512
  have eq4288 := Equation313_4512_implies_Equation4288 G eq313 eq4512
  have eq4291 := Equation313_4512_implies_Equation4291 G eq313 eq4512
  have eq4293 := Equation313_4512_implies_Equation4293 G eq313 eq4512
  have eq4296 := Equation313_4512_implies_Equation4296 G eq313 eq4512
  have eq4299 := Equation313_4512_implies_Equation4299 G eq313 eq4512
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4304 := Equation313_4512_implies_Equation4304 G eq313 eq4512
  have eq4305 := Equation313_4512_implies_Equation4305 G eq313 eq4512
  have eq4314 := Equation313_4512_implies_Equation4314 G eq313 eq4512
  have eq4318 := Equation313_4512_implies_Equation4318 G eq313 eq4512
  have eq4320 := Equation313_4512_implies_Equation4320 G eq313 eq4512
  have eq4321 := Equation313_4512_implies_Equation4321 G eq313 eq4512
  have eq4325 := Equation313_4512_implies_Equation4325 G eq313 eq4512
  have eq4327 := Equation313_4512_implies_Equation4327 G eq313 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq4343 := Equation313_4512_implies_Equation4343 G eq313 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4512⟩

theorem AT31_implied_by_long (G : Type*) [Magma G] : AssociativeTheory31_long G -> AssociativeTheory31 G :=
fun ⟨_, h40, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h309, h4512⟩

theorem AT31_equiv (G : Type*) [Magma G] : AssociativeTheory31 G <-> AssociativeTheory31_long G :=
Iff.intro (AT31_implies_long G) (AT31_implied_by_long G)

theorem AT32_implies_long (G : Type*) [Magma G] (h : AssociativeTheory32 G) : AssociativeTheory32_long G := by
  obtain ⟨eq308, eq309, eq4512⟩ := h
  have eq3265 := Equation308_309_4512_implies_Equation3265 G eq308 eq309 eq4512
  have eq3260 := Equation308_309_4512_implies_Equation3260 G eq308 eq309 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3253 := Equation3265_4512_implies_Equation3253 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq3261 := Equation3265_4512_implies_Equation3261 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact ⟨eq1, eq307, eq308, eq309, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4512⟩

theorem AT32_implied_by_long (G : Type*) [Magma G] : AssociativeTheory32_long G -> AssociativeTheory32 G :=
fun ⟨_, _, h308, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h308, h309, h4512⟩

theorem AT32_equiv (G : Type*) [Magma G] : AssociativeTheory32 G <-> AssociativeTheory32_long G :=
Iff.intro (AT32_implies_long G) (AT32_implied_by_long G)

theorem AT33_implies_long (G : Type*) [Magma G] (h : AssociativeTheory33 G) : AssociativeTheory33_long G := by
  obtain ⟨eq310, eq4512⟩ := h
  have eq1 := Equation310_4512_implies_Equation1 G eq310 eq4512
  have eq307 := Equation310_4512_implies_Equation307 G eq310 eq4512
  have eq308 := Equation310_4512_implies_Equation308 G eq310 eq4512
  have eq3253 := Equation310_4512_implies_Equation3253 G eq310 eq4512
  have eq3255 := Equation310_4512_implies_Equation3255 G eq310 eq4512
  have eq3256 := Equation310_4512_implies_Equation3256 G eq310 eq4512
  have eq3258 := Equation310_4512_implies_Equation3258 G eq310 eq4512
  have eq3259 := Equation310_4512_implies_Equation3259 G eq310 eq4512
  have eq3261 := Equation310_4512_implies_Equation3261 G eq310 eq4512
  have eq4268 := Equation310_4512_implies_Equation4268 G eq310 eq4512
  have eq4270 := Equation310_4512_implies_Equation4270 G eq310 eq4512
  have eq4284 := Equation310_4512_implies_Equation4284 G eq310 eq4512
  have eq4288 := Equation310_4512_implies_Equation4288 G eq310 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT33_implied_by_long (G : Type*) [Magma G] : AssociativeTheory33_long G -> AssociativeTheory33 G :=
fun ⟨_, _, _, h310, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h310, h4512⟩

theorem AT33_equiv (G : Type*) [Magma G] : AssociativeTheory33 G <-> AssociativeTheory33_long G :=
Iff.intro (AT33_implies_long G) (AT33_implied_by_long G)

theorem AT34_implies_long (G : Type*) [Magma G] (h : AssociativeTheory34 G) : AssociativeTheory34_long G := by
  obtain ⟨eq311, eq4512⟩ := h
  have eq1 := Equation311_4512_implies_Equation1 G eq311 eq4512
  have eq307 := Equation311_4512_implies_Equation307 G eq311 eq4512
  have eq308 := Equation311_4512_implies_Equation308 G eq311 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq310 := Equation311_4512_implies_Equation310 G eq311 eq4512
  have eq3253 := Equation311_4512_implies_Equation3253 G eq311 eq4512
  have eq3255 := Equation311_4512_implies_Equation3255 G eq311 eq4512
  have eq3256 := Equation311_4512_implies_Equation3256 G eq311 eq4512
  have eq3258 := Equation311_4512_implies_Equation3258 G eq311 eq4512
  have eq3259 := Equation311_4512_implies_Equation3259 G eq311 eq4512
  have eq3260 := Equation311_4512_implies_Equation3260 G eq311 eq4512
  have eq3261 := Equation311_4512_implies_Equation3261 G eq311 eq4512
  have eq3264 := Equation311_4512_implies_Equation3264 G eq311 eq4512
  have eq3265 := Equation311_4512_implies_Equation3265 G eq311 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq4268 := Equation311_4512_implies_Equation4268 G eq311 eq4512
  have eq4269 := Equation311_4512_implies_Equation4269 G eq311 eq4512
  have eq4270 := Equation311_4512_implies_Equation4270 G eq311 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4283 := Equation311_4512_implies_Equation4283 G eq311 eq4512
  have eq4284 := Equation311_4512_implies_Equation4284 G eq311 eq4512
  have eq4286 := Equation311_4512_implies_Equation4286 G eq311 eq4512
  have eq4287 := Equation311_4512_implies_Equation4287 G eq311 eq4512
  have eq4288 := Equation311_4512_implies_Equation4288 G eq311 eq4512
  have eq4314 := Equation311_4512_implies_Equation4314 G eq311 eq4512
  have eq4315 := Equation311_4512_implies_Equation4315 G eq311 eq4512
  have eq4318 := Equation311_4512_implies_Equation4318 G eq311 eq4512
  have eq4358 := Equation311_4512_implies_Equation4358 G eq311 eq4512
  exact ⟨eq1, eq307, eq308, eq309, eq310, eq311, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq4268, eq4269, eq4270, eq4271, eq4283, eq4284, eq4286, eq4287, eq4288, eq4314, eq4315, eq4318, eq4358, eq4512⟩

theorem AT34_implied_by_long (G : Type*) [Magma G] : AssociativeTheory34_long G -> AssociativeTheory34 G :=
fun ⟨_, _, _, _, _, h311, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h311, h4512⟩

theorem AT34_equiv (G : Type*) [Magma G] : AssociativeTheory34 G <-> AssociativeTheory34_long G :=
Iff.intro (AT34_implies_long G) (AT34_implied_by_long G)

theorem AT35_implies_long (G : Type*) [Magma G] (h : AssociativeTheory35 G) : AssociativeTheory35_long G := by
  obtain ⟨eq40, eq311, eq4512⟩ := h
  have eq314 := Equation40_311_4512_implies_Equation314 G eq40 eq311 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation314_4512_implies_Equation307 G eq314 eq4512
  have eq308 := Equation314_4512_implies_Equation308 G eq314 eq4512
  have eq309 := Equation314_4512_implies_Equation309 G eq314 eq4512
  have eq310 := Equation314_4512_implies_Equation310 G eq314 eq4512
  have eq312 := Equation314_4512_implies_Equation312 G eq314 eq4512
  have eq313 := Equation314_4512_implies_Equation313 G eq314 eq4512
  have eq315 := Equation314_4512_implies_Equation315 G eq314 eq4512
  have eq316 := Equation314_4512_implies_Equation316 G eq314 eq4512
  have eq318 := Equation314_4512_implies_Equation318 G eq314 eq4512
  have eq3255 := Equation314_4512_implies_Equation3255 G eq314 eq4512
  have eq3258 := Equation314_4512_implies_Equation3258 G eq314 eq4512
  have eq3260 := Equation314_4512_implies_Equation3260 G eq314 eq4512
  have eq3264 := Equation314_4512_implies_Equation3264 G eq314 eq4512
  have eq3265 := Equation314_4512_implies_Equation3265 G eq314 eq4512
  have eq3267 := Equation314_4512_implies_Equation3267 G eq314 eq4512
  have eq3273 := Equation314_4512_implies_Equation3273 G eq314 eq4512
  have eq3274 := Equation314_4512_implies_Equation3274 G eq314 eq4512
  have eq3275 := Equation314_4512_implies_Equation3275 G eq314 eq4512
  have eq3277 := Equation314_4512_implies_Equation3277 G eq314 eq4512
  have eq3290 := Equation314_4512_implies_Equation3290 G eq314 eq4512
  have eq3292 := Equation314_4512_implies_Equation3292 G eq314 eq4512
  have eq3300 := Equation314_4512_implies_Equation3300 G eq314 eq4512
  have eq4268 := Equation314_4512_implies_Equation4268 G eq314 eq4512
  have eq4269 := Equation314_4512_implies_Equation4269 G eq314 eq4512
  have eq4271 := Equation314_4512_implies_Equation4271 G eq314 eq4512
  have eq4272 := Equation314_4512_implies_Equation4272 G eq314 eq4512
  have eq4273 := Equation314_4512_implies_Equation4273 G eq314 eq4512
  have eq4274 := Equation314_4512_implies_Equation4274 G eq314 eq4512
  have eq4276 := Equation314_4512_implies_Equation4276 G eq314 eq4512
  have eq4277 := Equation314_4512_implies_Equation4277 G eq314 eq4512
  have eq4278 := Equation314_4512_implies_Equation4278 G eq314 eq4512
  have eq4279 := Equation314_4512_implies_Equation4279 G eq314 eq4512
  have eq4280 := Equation314_4512_implies_Equation4280 G eq314 eq4512
  have eq4283 := Equation314_4512_implies_Equation4283 G eq314 eq4512
  have eq4284 := Equation314_4512_implies_Equation4284 G eq314 eq4512
  have eq4286 := Equation314_4512_implies_Equation4286 G eq314 eq4512
  have eq4287 := Equation314_4512_implies_Equation4287 G eq314 eq4512
  have eq4288 := Equation314_4512_implies_Equation4288 G eq314 eq4512
  have eq4291 := Equation314_4512_implies_Equation4291 G eq314 eq4512
  have eq4293 := Equation314_4512_implies_Equation4293 G eq314 eq4512
  have eq4296 := Equation314_4512_implies_Equation4296 G eq314 eq4512
  have eq4299 := Equation314_4512_implies_Equation4299 G eq314 eq4512
  have eq4300 := Equation314_4512_implies_Equation4300 G eq314 eq4512
  have eq4301 := Equation314_4512_implies_Equation4301 G eq314 eq4512
  have eq4304 := Equation314_4512_implies_Equation4304 G eq314 eq4512
  have eq4305 := Equation314_4512_implies_Equation4305 G eq314 eq4512
  have eq4314 := Equation314_4512_implies_Equation4314 G eq314 eq4512
  have eq4315 := Equation314_4512_implies_Equation4315 G eq314 eq4512
  have eq4318 := Equation314_4512_implies_Equation4318 G eq314 eq4512
  have eq4320 := Equation314_4512_implies_Equation4320 G eq314 eq4512
  have eq4321 := Equation314_4512_implies_Equation4321 G eq314 eq4512
  have eq4325 := Equation314_4512_implies_Equation4325 G eq314 eq4512
  have eq4327 := Equation314_4512_implies_Equation4327 G eq314 eq4512
  have eq4331 := Equation314_4512_implies_Equation4331 G eq314 eq4512
  have eq4343 := Equation314_4512_implies_Equation4343 G eq314 eq4512
  have eq4358 := Equation314_4512_implies_Equation4358 G eq314 eq4512
  have eq4362 := Equation314_4512_implies_Equation4362 G eq314 eq4512
  have eq4364 := Equation314_4512_implies_Equation4364 G eq314 eq4512
  have eq4369 := Equation314_4512_implies_Equation4369 G eq314 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq311, eq312, eq313, eq314, eq315, eq316, eq318, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4271, eq4272, eq4273, eq4274, eq4275, eq4276, eq4277, eq4278, eq4279, eq4280, eq4283, eq4284, eq4286, eq4287, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4300, eq4301, eq4304, eq4305, eq4314, eq4315, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT35_implied_by_long (G : Type*) [Magma G] : AssociativeTheory35_long G -> AssociativeTheory35 G :=
fun ⟨_, h40, _, _, _, _, h311, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h311, h4512⟩

theorem AT35_equiv (G : Type*) [Magma G] : AssociativeTheory35 G <-> AssociativeTheory35_long G :=
Iff.intro (AT35_implies_long G) (AT35_implied_by_long G)

theorem AT36_implies_long (G : Type*) [Magma G] (h : AssociativeTheory36 G) : AssociativeTheory36_long G := by
  obtain ⟨eq43, eq311, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq307 := Equation311_4512_implies_Equation307 G eq311 eq4512
  have eq308 := Equation311_4512_implies_Equation308 G eq311 eq4512
  have eq309 := Equation311_4512_implies_Equation309 G eq311 eq4512
  have eq310 := Equation311_4512_implies_Equation310 G eq311 eq4512
  have eq3253 := Equation311_4512_implies_Equation3253 G eq311 eq4512
  have eq3255 := Equation311_4512_implies_Equation3255 G eq311 eq4512
  have eq3256 := Equation311_4512_implies_Equation3256 G eq311 eq4512
  have eq3258 := Equation311_4512_implies_Equation3258 G eq311 eq4512
  have eq3259 := Equation311_4512_implies_Equation3259 G eq311 eq4512
  have eq3260 := Equation311_4512_implies_Equation3260 G eq311 eq4512
  have eq3261 := Equation311_4512_implies_Equation3261 G eq311 eq4512
  have eq3264 := Equation311_4512_implies_Equation3264 G eq311 eq4512
  have eq3265 := Equation311_4512_implies_Equation3265 G eq311 eq4512
  have eq3267 := Equation311_4512_implies_Equation3267 G eq311 eq4512
  have eq4268 := Equation311_4512_implies_Equation4268 G eq311 eq4512
  have eq4269 := Equation311_4512_implies_Equation4269 G eq311 eq4512
  have eq4270 := Equation311_4512_implies_Equation4270 G eq311 eq4512
  have eq4271 := Equation311_4512_implies_Equation4271 G eq311 eq4512
  have eq4284 := Equation311_4512_implies_Equation4284 G eq311 eq4512
  have eq4286 := Equation311_4512_implies_Equation4286 G eq311 eq4512
  have eq4287 := Equation311_4512_implies_Equation4287 G eq311 eq4512
  have eq4288 := Equation311_4512_implies_Equation4288 G eq311 eq4512
  have eq4314 := Equation311_4512_implies_Equation4314 G eq311 eq4512
  have eq4315 := Equation311_4512_implies_Equation4315 G eq311 eq4512
  have eq4318 := Equation311_4512_implies_Equation4318 G eq311 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq40 := Equation3255_4290_4512_implies_Equation40 G eq3255 eq4290 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq314 := Equation40_311_4512_implies_Equation314 G eq40 eq311 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4274 := Equation4271_4272_4512_implies_Equation4274 G eq4271 eq4272 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4278 := Equation4272_4287_4512_implies_Equation4278 G eq4272 eq4287 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq318 := Equation312_4287_4512_implies_Equation318 G eq312 eq4287 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4276 := Equation313_4512_implies_Equation4276 G eq313 eq4512
  have eq3300 := Equation314_4512_implies_Equation3300 G eq314 eq4512
  have eq4300 := Equation314_4512_implies_Equation4300 G eq314 eq4512
  exact ⟨eq1, eq40, eq43, eq307, eq308, eq309, eq310, eq311, eq312, eq313, eq314, eq315, eq316, eq318, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4271, eq4272, eq4273, eq4274, eq4275, eq4276, eq4277, eq4278, eq4279, eq4280, eq4283, eq4284, eq4286, eq4287, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4300, eq4301, eq4304, eq4305, eq4314, eq4315, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT36_implied_by_long (G : Type*) [Magma G] : AssociativeTheory36_long G -> AssociativeTheory36 G :=
fun ⟨_, _, h43, _, _, _, _, h311, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h311, h4512⟩

theorem AT36_equiv (G : Type*) [Magma G] : AssociativeTheory36 G <-> AssociativeTheory36_long G :=
Iff.intro (AT36_implies_long G) (AT36_implied_by_long G)

theorem AT37_implies_long (G : Type*) [Magma G] (h : AssociativeTheory37 G) : AssociativeTheory37_long G := by
  obtain ⟨eq312, eq4512⟩ := h
  have eq1 := Equation312_4512_implies_Equation1 G eq312 eq4512
  have eq307 := Equation312_4512_implies_Equation307 G eq312 eq4512
  have eq3253 := Equation312_4512_implies_Equation3253 G eq312 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  exact ⟨eq1, eq307, eq312, eq3253, eq3258, eq3278, eq4272, eq4512⟩

theorem AT37_implied_by_long (G : Type*) [Magma G] : AssociativeTheory37_long G -> AssociativeTheory37 G :=
fun ⟨_, _, h312, _, _, _, _, h4512⟩ => ⟨h312, h4512⟩

theorem AT37_equiv (G : Type*) [Magma G] : AssociativeTheory37 G <-> AssociativeTheory37_long G :=
Iff.intro (AT37_implies_long G) (AT37_implied_by_long G)

theorem AT38_implies_long (G : Type*) [Magma G] (h : AssociativeTheory38 G) : AssociativeTheory38_long G := by
  obtain ⟨eq309, eq312, eq4512⟩ := h
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation309_4512_implies_Equation307 G eq309 eq4512
  have eq3253 := Equation309_4512_implies_Equation3253 G eq309 eq4512
  have eq3255 := Equation309_4512_implies_Equation3255 G eq309 eq4512
  have eq3258 := Equation309_4512_implies_Equation3258 G eq309 eq4512
  have eq3261 := Equation309_4512_implies_Equation3261 G eq309 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4284 := Equation309_4512_implies_Equation4284 G eq309 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation3274_4512_implies_Equation3271 G eq3274 eq4512
  have eq4275 := Equation3274_4512_implies_Equation4275 G eq3274 eq4512
  have eq4304 := Equation3274_4512_implies_Equation4304 G eq3274 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  exact ⟨eq1, eq307, eq309, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4512⟩

theorem AT38_implied_by_long (G : Type*) [Magma G] : AssociativeTheory38_long G -> AssociativeTheory38 G :=
fun ⟨_, _, h309, h312, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h312, h4512⟩

theorem AT38_equiv (G : Type*) [Magma G] : AssociativeTheory38 G <-> AssociativeTheory38_long G :=
Iff.intro (AT38_implies_long G) (AT38_implied_by_long G)

theorem AT39_implies_long (G : Type*) [Magma G] (h : AssociativeTheory39 G) : AssociativeTheory39_long G := by
  obtain ⟨eq315, eq4512⟩ := h
  have eq1 := Equation315_4512_implies_Equation1 G eq315 eq4512
  have eq307 := Equation315_4512_implies_Equation307 G eq315 eq4512
  have eq312 := Equation315_4512_implies_Equation312 G eq315 eq4512
  have eq3253 := Equation315_4512_implies_Equation3253 G eq315 eq4512
  have eq3255 := Equation315_4512_implies_Equation3255 G eq315 eq4512
  have eq3258 := Equation315_4512_implies_Equation3258 G eq315 eq4512
  have eq3261 := Equation315_4512_implies_Equation3261 G eq315 eq4512
  have eq3271 := Equation315_4512_implies_Equation3271 G eq315 eq4512
  have eq3278 := Equation315_4512_implies_Equation3278 G eq315 eq4512
  have eq4272 := Equation315_4512_implies_Equation4272 G eq315 eq4512
  have eq4275 := Equation315_4512_implies_Equation4275 G eq315 eq4512
  have eq4284 := Equation315_4512_implies_Equation4284 G eq315 eq4512
  have eq4304 := Equation315_4512_implies_Equation4304 G eq315 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3271, eq3278, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT39_implied_by_long (G : Type*) [Magma G] : AssociativeTheory39_long G -> AssociativeTheory39 G :=
fun ⟨_, _, _, h315, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h315, h4512⟩

theorem AT39_equiv (G : Type*) [Magma G] : AssociativeTheory39 G <-> AssociativeTheory39_long G :=
Iff.intro (AT39_implies_long G) (AT39_implied_by_long G)

theorem AT40_implies_long (G : Type*) [Magma G] (h : AssociativeTheory40 G) : AssociativeTheory40_long G := by
  obtain ⟨eq318, eq4512⟩ := h
  have eq1 := Equation318_4512_implies_Equation1 G eq318 eq4512
  have eq307 := Equation318_4512_implies_Equation307 G eq318 eq4512
  have eq309 := Equation318_4512_implies_Equation309 G eq318 eq4512
  have eq312 := Equation318_4512_implies_Equation312 G eq318 eq4512
  have eq315 := Equation318_4512_implies_Equation315 G eq318 eq4512
  have eq3253 := Equation318_4512_implies_Equation3253 G eq318 eq4512
  have eq3255 := Equation318_4512_implies_Equation3255 G eq318 eq4512
  have eq3258 := Equation318_4512_implies_Equation3258 G eq318 eq4512
  have eq3261 := Equation318_4512_implies_Equation3261 G eq318 eq4512
  have eq3264 := Equation318_4512_implies_Equation3264 G eq318 eq4512
  have eq3271 := Equation318_4512_implies_Equation3271 G eq318 eq4512
  have eq3274 := Equation318_4512_implies_Equation3274 G eq318 eq4512
  have eq3278 := Equation318_4512_implies_Equation3278 G eq318 eq4512
  have eq3292 := Equation318_4512_implies_Equation3292 G eq318 eq4512
  have eq3300 := Equation318_4512_implies_Equation3300 G eq318 eq4512
  have eq4269 := Equation318_4512_implies_Equation4269 G eq318 eq4512
  have eq4272 := Equation318_4512_implies_Equation4272 G eq318 eq4512
  have eq4275 := Equation318_4512_implies_Equation4275 G eq318 eq4512
  have eq4278 := Equation318_4512_implies_Equation4278 G eq318 eq4512
  have eq4284 := Equation318_4512_implies_Equation4284 G eq318 eq4512
  have eq4287 := Equation318_4512_implies_Equation4287 G eq318 eq4512
  have eq4291 := Equation318_4512_implies_Equation4291 G eq318 eq4512
  have eq4296 := Equation318_4512_implies_Equation4296 G eq318 eq4512
  have eq4300 := Equation318_4512_implies_Equation4300 G eq318 eq4512
  have eq4304 := Equation318_4512_implies_Equation4304 G eq318 eq4512
  have eq4320 := Equation318_4512_implies_Equation4320 G eq318 eq4512
  have eq4327 := Equation318_4512_implies_Equation4327 G eq318 eq4512
  have eq4362 := Equation318_4512_implies_Equation4362 G eq318 eq4512
  exact ⟨eq1, eq307, eq309, eq312, eq315, eq318, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq3300, eq4269, eq4272, eq4275, eq4278, eq4284, eq4287, eq4291, eq4296, eq4300, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT40_implied_by_long (G : Type*) [Magma G] : AssociativeTheory40_long G -> AssociativeTheory40 G :=
fun ⟨_, _, _, _, _, h318, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h318, h4512⟩

theorem AT40_equiv (G : Type*) [Magma G] : AssociativeTheory40 G <-> AssociativeTheory40_long G :=
Iff.intro (AT40_implies_long G) (AT40_implied_by_long G)

theorem AT41_implies_long (G : Type*) [Magma G] (h : AssociativeTheory41 G) : AssociativeTheory41_long G := by
  obtain ⟨eq323, eq4512⟩ := h
  have eq1 := Equation323_4512_implies_Equation1 G eq323 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4512⟩

theorem AT41_implied_by_long (G : Type*) [Magma G] : AssociativeTheory41_long G -> AssociativeTheory41 G :=
fun ⟨_, _, h323, _, _, h4512⟩ => ⟨h323, h4512⟩

theorem AT41_equiv (G : Type*) [Magma G] : AssociativeTheory41 G <-> AssociativeTheory41_long G :=
Iff.intro (AT41_implies_long G) (AT41_implied_by_long G)

theorem AT42_implies_long (G : Type*) [Magma G] (h : AssociativeTheory42 G) : AssociativeTheory42_long G := by
  obtain ⟨eq43, eq323, eq4512⟩ := h
  have eq332 := Equation43_323_4512_implies_Equation332 G eq43 eq323 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq325 := Equation332_4512_implies_Equation325 G eq332 eq4512
  have eq326 := Equation332_4512_implies_Equation326 G eq332 eq4512
  have eq333 := Equation332_4512_implies_Equation333 G eq332 eq4512
  have eq3308 := Equation332_4512_implies_Equation3308 G eq332 eq4512
  have eq3309 := Equation332_4512_implies_Equation3309 G eq332 eq4512
  have eq3315 := Equation332_4512_implies_Equation3315 G eq332 eq4512
  have eq3316 := Equation332_4512_implies_Equation3316 G eq332 eq4512
  have eq3319 := Equation332_4512_implies_Equation3319 G eq332 eq4512
  have eq3342 := Equation332_4512_implies_Equation3342 G eq332 eq4512
  have eq3346 := Equation332_4512_implies_Equation3346 G eq332 eq4512
  have eq3353 := Equation332_4512_implies_Equation3353 G eq332 eq4512
  have eq4284 := Equation332_4512_implies_Equation4284 G eq332 eq4512
  have eq4291 := Equation332_4512_implies_Equation4291 G eq332 eq4512
  have eq4293 := Equation332_4512_implies_Equation4293 G eq332 eq4512
  have eq4314 := Equation332_4512_implies_Equation4314 G eq332 eq4512
  have eq4321 := Equation332_4512_implies_Equation4321 G eq332 eq4512
  have eq4343 := Equation332_4512_implies_Equation4343 G eq332 eq4512
  exact ⟨eq1, eq43, eq307, eq323, eq325, eq326, eq332, eq333, eq3253, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq3342, eq3346, eq3353, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT42_implied_by_long (G : Type*) [Magma G] : AssociativeTheory42_long G -> AssociativeTheory42 G :=
fun ⟨_, h43, _, h323, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h323, h4512⟩

theorem AT42_equiv (G : Type*) [Magma G] : AssociativeTheory42 G <-> AssociativeTheory42_long G :=
Iff.intro (AT42_implies_long G) (AT42_implied_by_long G)

theorem AT43_implies_long (G : Type*) [Magma G] (h : AssociativeTheory43 G) : AssociativeTheory43_long G := by
  obtain ⟨eq309, eq323, eq4512⟩ := h
  have eq329 := Equation309_323_4512_implies_Equation329 G eq309 eq323 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation329_4512_implies_Equation307 G eq329 eq4512
  have eq326 := Equation329_4512_implies_Equation326 G eq329 eq4512
  have eq3253 := Equation329_4512_implies_Equation3253 G eq329 eq4512
  have eq3255 := Equation329_4512_implies_Equation3255 G eq329 eq4512
  have eq3258 := Equation329_4512_implies_Equation3258 G eq329 eq4512
  have eq3261 := Equation329_4512_implies_Equation3261 G eq329 eq4512
  have eq3264 := Equation329_4512_implies_Equation3264 G eq329 eq4512
  have eq3306 := Equation329_4512_implies_Equation3306 G eq329 eq4512
  have eq3309 := Equation329_4512_implies_Equation3309 G eq329 eq4512
  have eq3316 := Equation329_4512_implies_Equation3316 G eq329 eq4512
  have eq3319 := Equation329_4512_implies_Equation3319 G eq329 eq4512
  have eq3322 := Equation329_4512_implies_Equation3322 G eq329 eq4512
  have eq3326 := Equation329_4512_implies_Equation3326 G eq329 eq4512
  have eq3334 := Equation329_4512_implies_Equation3334 G eq329 eq4512
  have eq4269 := Equation329_4512_implies_Equation4269 G eq329 eq4512
  have eq4284 := Equation329_4512_implies_Equation4284 G eq329 eq4512
  have eq4287 := Equation329_4512_implies_Equation4287 G eq329 eq4512
  exact ⟨eq1, eq307, eq309, eq323, eq326, eq329, eq3253, eq3255, eq3258, eq3261, eq3264, eq3306, eq3309, eq3316, eq3319, eq3322, eq3326, eq3334, eq4269, eq4284, eq4287, eq4512⟩

theorem AT43_implied_by_long (G : Type*) [Magma G] : AssociativeTheory43_long G -> AssociativeTheory43 G :=
fun ⟨_, _, h309, h323, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h323, h4512⟩

theorem AT43_equiv (G : Type*) [Magma G] : AssociativeTheory43 G <-> AssociativeTheory43_long G :=
Iff.intro (AT43_implies_long G) (AT43_implied_by_long G)

theorem AT44_implies_long (G : Type*) [Magma G] (h : AssociativeTheory44 G) : AssociativeTheory44_long G := by
  obtain ⟨eq312, eq323, eq4512⟩ := h
  have eq343 := Equation312_323_4512_implies_Equation343 G eq312 eq323 eq4512
  have eq1 := Equation312_4512_implies_Equation1 G eq312 eq4512
  have eq307 := Equation312_4512_implies_Equation307 G eq312 eq4512
  have eq3253 := Equation312_4512_implies_Equation3253 G eq312 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq333 := Equation343_4512_implies_Equation333 G eq343 eq4512
  have eq3316 := Equation343_4512_implies_Equation3316 G eq343 eq4512
  have eq3326 := Equation343_4512_implies_Equation3326 G eq343 eq4512
  have eq3353 := Equation343_4512_implies_Equation3353 G eq343 eq4512
  have eq3414 := Equation343_4512_implies_Equation3414 G eq343 eq4512
  have eq4291 := Equation343_4512_implies_Equation4291 G eq343 eq4512
  have eq4300 := Equation343_4512_implies_Equation4300 G eq343 eq4512
  exact ⟨eq1, eq307, eq312, eq323, eq333, eq343, eq3253, eq3258, eq3278, eq3306, eq3316, eq3326, eq3353, eq3414, eq4272, eq4291, eq4300, eq4512⟩

theorem AT44_implied_by_long (G : Type*) [Magma G] : AssociativeTheory44_long G -> AssociativeTheory44 G :=
fun ⟨_, _, h312, h323, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h312, h323, h4512⟩

theorem AT44_equiv (G : Type*) [Magma G] : AssociativeTheory44 G <-> AssociativeTheory44_long G :=
Iff.intro (AT44_implies_long G) (AT44_implied_by_long G)

theorem AT45_implies_long (G : Type*) [Magma G] (h : AssociativeTheory45 G) : AssociativeTheory45_long G := by
  obtain ⟨eq325, eq4512⟩ := h
  have eq1 := Equation325_4512_implies_Equation1 G eq325 eq4512
  have eq307 := Equation325_4512_implies_Equation307 G eq325 eq4512
  have eq326 := Equation325_4512_implies_Equation326 G eq325 eq4512
  have eq3253 := Equation325_4512_implies_Equation3253 G eq325 eq4512
  have eq3315 := Equation325_4512_implies_Equation3315 G eq325 eq4512
  have eq3316 := Equation325_4512_implies_Equation3316 G eq325 eq4512
  have eq3319 := Equation325_4512_implies_Equation3319 G eq325 eq4512
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  exact ⟨eq1, eq307, eq325, eq326, eq3253, eq3315, eq3316, eq3319, eq4314, eq4512⟩

theorem AT45_implied_by_long (G : Type*) [Magma G] : AssociativeTheory45_long G -> AssociativeTheory45 G :=
fun ⟨_, _, h325, _, _, _, _, _, _, h4512⟩ => ⟨h325, h4512⟩

theorem AT45_equiv (G : Type*) [Magma G] : AssociativeTheory45 G <-> AssociativeTheory45_long G :=
Iff.intro (AT45_implies_long G) (AT45_implied_by_long G)

theorem AT46_implies_long (G : Type*) [Magma G] (h : AssociativeTheory46 G) : AssociativeTheory46_long G := by
  obtain ⟨eq3, eq325, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  have eq307 := Equation3_4512_implies_Equation307 G eq3 eq4512
  have eq323 := Equation3_4512_implies_Equation323 G eq3 eq4512
  have eq326 := Equation3_4512_implies_Equation326 G eq3 eq4512
  have eq411 := Equation3_4512_implies_Equation411 G eq3 eq4512
  have eq3253 := Equation3_4512_implies_Equation3253 G eq3 eq4512
  have eq3306 := Equation3_4512_implies_Equation3306 G eq3 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3_4512_implies_Equation3316 G eq3 eq4512
  have eq3319 := Equation3_4512_implies_Equation3319 G eq3 eq4512
  have eq4284 := Equation3_4512_implies_Equation4284 G eq3 eq4512
  have eq3315 := Equation325_4512_implies_Equation3315 G eq325 eq4512
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  have eq4283 := Equation4284_4314_4512_implies_Equation4283 G eq4284 eq4314 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  exact ⟨eq1, eq3, eq8, eq47, eq307, eq323, eq325, eq326, eq411, eq3253, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq4283, eq4284, eq4314, eq4512⟩

theorem AT46_implied_by_long (G : Type*) [Magma G] : AssociativeTheory46_long G -> AssociativeTheory46 G :=
fun ⟨_, h3, _, _, _, _, h325, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h325, h4512⟩

theorem AT46_equiv (G : Type*) [Magma G] : AssociativeTheory46 G <-> AssociativeTheory46_long G :=
Iff.intro (AT46_implies_long G) (AT46_implied_by_long G)

theorem AT47_implies_long (G : Type*) [Magma G] (h : AssociativeTheory47 G) : AssociativeTheory47_long G := by
  obtain ⟨eq308, eq325, eq4512⟩ := h
  have eq327 := Equation308_325_4512_implies_Equation327 G eq308 eq325 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation308_4512_implies_Equation307 G eq308 eq4512
  have eq3253 := Equation308_4512_implies_Equation3253 G eq308 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  have eq326 := Equation325_4512_implies_Equation326 G eq325 eq4512
  have eq3315 := Equation325_4512_implies_Equation3315 G eq325 eq4512
  have eq3316 := Equation325_4512_implies_Equation3316 G eq325 eq4512
  have eq3319 := Equation325_4512_implies_Equation3319 G eq325 eq4512
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  have eq3322 := Equation327_4512_implies_Equation3322 G eq327 eq4512
  have eq3323 := Equation327_4512_implies_Equation3323 G eq327 eq4512
  have eq4315 := Equation327_4512_implies_Equation4315 G eq327 eq4512
  exact ⟨eq1, eq307, eq308, eq325, eq326, eq327, eq3253, eq3255, eq3256, eq3315, eq3316, eq3319, eq3322, eq3323, eq4268, eq4314, eq4315, eq4512⟩

theorem AT47_implied_by_long (G : Type*) [Magma G] : AssociativeTheory47_long G -> AssociativeTheory47 G :=
fun ⟨_, _, h308, h325, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h308, h325, h4512⟩

theorem AT47_equiv (G : Type*) [Magma G] : AssociativeTheory47 G <-> AssociativeTheory47_long G :=
Iff.intro (AT47_implies_long G) (AT47_implied_by_long G)

theorem AT48_implies_long (G : Type*) [Magma G] (h : AssociativeTheory48 G) : AssociativeTheory48_long G := by
  obtain ⟨eq323, eq325, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq326 := Equation325_4512_implies_Equation326 G eq325 eq4512
  have eq3315 := Equation325_4512_implies_Equation3315 G eq325 eq4512
  have eq3316 := Equation325_4512_implies_Equation3316 G eq325 eq4512
  have eq3319 := Equation325_4512_implies_Equation3319 G eq325 eq4512
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  have eq3309 := Equation323_326_4512_implies_Equation3309 G eq323 eq326 eq4512
  have eq4284 := Equation3309_4512_implies_Equation4284 G eq3309 eq4512
  have eq4283 := Equation4284_4314_4512_implies_Equation4283 G eq4284 eq4314 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  exact ⟨eq1, eq307, eq323, eq325, eq326, eq3253, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq4283, eq4284, eq4314, eq4512⟩

theorem AT48_implied_by_long (G : Type*) [Magma G] : AssociativeTheory48_long G -> AssociativeTheory48 G :=
fun ⟨_, _, h323, h325, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h323, h325, h4512⟩

theorem AT48_equiv (G : Type*) [Magma G] : AssociativeTheory48 G <-> AssociativeTheory48_long G :=
Iff.intro (AT48_implies_long G) (AT48_implied_by_long G)

theorem AT49_implies_long (G : Type*) [Magma G] (h : AssociativeTheory49 G) : AssociativeTheory49_long G := by
  obtain ⟨eq326, eq4512⟩ := h
  have eq1 := Equation326_4512_implies_Equation1 G eq326 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4512⟩

theorem AT49_implied_by_long (G : Type*) [Magma G] : AssociativeTheory49_long G -> AssociativeTheory49 G :=
fun ⟨_, _, h326, _, _, h4512⟩ => ⟨h326, h4512⟩

theorem AT49_equiv (G : Type*) [Magma G] : AssociativeTheory49 G <-> AssociativeTheory49_long G :=
Iff.intro (AT49_implies_long G) (AT49_implied_by_long G)

theorem AT50_implies_long (G : Type*) [Magma G] (h : AssociativeTheory50 G) : AssociativeTheory50_long G := by
  obtain ⟨eq323, eq326, eq4512⟩ := h
  have eq3309 := Equation323_326_4512_implies_Equation3309 G eq323 eq326 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq3316 := Equation3309_4512_implies_Equation3316 G eq3309 eq4512
  have eq3319 := Equation3309_4512_implies_Equation3319 G eq3309 eq4512
  have eq4284 := Equation3309_4512_implies_Equation4284 G eq3309 eq4512
  exact ⟨eq1, eq307, eq323, eq326, eq3253, eq3306, eq3309, eq3316, eq3319, eq4284, eq4512⟩

theorem AT50_implied_by_long (G : Type*) [Magma G] : AssociativeTheory50_long G -> AssociativeTheory50 G :=
fun ⟨_, _, h323, h326, _, _, _, _, _, _, h4512⟩ => ⟨h323, h326, h4512⟩

theorem AT50_equiv (G : Type*) [Magma G] : AssociativeTheory50 G <-> AssociativeTheory50_long G :=
Iff.intro (AT50_implies_long G) (AT50_implied_by_long G)

theorem AT51_implies_long (G : Type*) [Magma G] (h : AssociativeTheory51 G) : AssociativeTheory51_long G := by
  obtain ⟨eq333, eq4512⟩ := h
  have eq1 := Equation333_4512_implies_Equation1 G eq333 eq4512
  have eq307 := Equation333_4512_implies_Equation307 G eq333 eq4512
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  have eq3253 := Equation333_4512_implies_Equation3253 G eq333 eq4512
  have eq3306 := Equation333_4512_implies_Equation3306 G eq333 eq4512
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  have eq3353 := Equation333_4512_implies_Equation3353 G eq333 eq4512
  have eq4291 := Equation333_4512_implies_Equation4291 G eq333 eq4512
  exact ⟨eq1, eq307, eq323, eq333, eq3253, eq3306, eq3316, eq3353, eq4291, eq4512⟩

theorem AT51_implied_by_long (G : Type*) [Magma G] : AssociativeTheory51_long G -> AssociativeTheory51 G :=
fun ⟨_, _, _, h333, _, _, _, _, _, h4512⟩ => ⟨h333, h4512⟩

theorem AT51_equiv (G : Type*) [Magma G] : AssociativeTheory51 G <-> AssociativeTheory51_long G :=
Iff.intro (AT51_implies_long G) (AT51_implied_by_long G)

theorem AT52_implies_long (G : Type*) [Magma G] (h : AssociativeTheory52 G) : AssociativeTheory52_long G := by
  obtain ⟨eq3, eq333, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  have eq307 := Equation3_4512_implies_Equation307 G eq3 eq4512
  have eq323 := Equation3_4512_implies_Equation323 G eq3 eq4512
  have eq326 := Equation3_4512_implies_Equation326 G eq3 eq4512
  have eq411 := Equation3_4512_implies_Equation411 G eq3 eq4512
  have eq3253 := Equation3_4512_implies_Equation3253 G eq3 eq4512
  have eq3306 := Equation3_4512_implies_Equation3306 G eq3 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3_4512_implies_Equation3316 G eq3 eq4512
  have eq3319 := Equation3_4512_implies_Equation3319 G eq3 eq4512
  have eq4284 := Equation3_4512_implies_Equation4284 G eq3 eq4512
  have eq3353 := Equation333_4512_implies_Equation3353 G eq333 eq4512
  have eq4291 := Equation333_4512_implies_Equation4291 G eq333 eq4512
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  exact ⟨eq1, eq3, eq8, eq47, eq307, eq323, eq326, eq333, eq411, eq3253, eq3306, eq3309, eq3316, eq3319, eq3346, eq3353, eq4284, eq4291, eq4320, eq4512⟩

theorem AT52_implied_by_long (G : Type*) [Magma G] : AssociativeTheory52_long G -> AssociativeTheory52 G :=
fun ⟨_, h3, _, _, _, _, _, h333, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h333, h4512⟩

theorem AT52_equiv (G : Type*) [Magma G] : AssociativeTheory52 G <-> AssociativeTheory52_long G :=
Iff.intro (AT52_implies_long G) (AT52_implied_by_long G)

theorem AT53_implies_long (G : Type*) [Magma G] (h : AssociativeTheory53 G) : AssociativeTheory53_long G := by
  obtain ⟨eq326, eq333, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation333_4512_implies_Equation307 G eq333 eq4512
  have eq323 := Equation333_4512_implies_Equation323 G eq333 eq4512
  have eq3253 := Equation333_4512_implies_Equation3253 G eq333 eq4512
  have eq3306 := Equation333_4512_implies_Equation3306 G eq333 eq4512
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  have eq3353 := Equation333_4512_implies_Equation3353 G eq333 eq4512
  have eq4291 := Equation333_4512_implies_Equation4291 G eq333 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  have eq3309 := Equation323_326_4512_implies_Equation3309 G eq323 eq326 eq4512
  have eq4284 := Equation3309_4512_implies_Equation4284 G eq3309 eq4512
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  exact ⟨eq1, eq307, eq323, eq326, eq333, eq3253, eq3306, eq3309, eq3316, eq3319, eq3346, eq3353, eq4284, eq4291, eq4320, eq4512⟩

theorem AT53_implied_by_long (G : Type*) [Magma G] : AssociativeTheory53_long G -> AssociativeTheory53 G :=
fun ⟨_, _, _, h326, h333, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h326, h333, h4512⟩

theorem AT53_equiv (G : Type*) [Magma G] : AssociativeTheory53 G <-> AssociativeTheory53_long G :=
Iff.intro (AT53_implies_long G) (AT53_implied_by_long G)

theorem AT54_implies_long (G : Type*) [Magma G] (h : AssociativeTheory54 G) : AssociativeTheory54_long G := by
  obtain ⟨eq411, eq4512⟩ := h
  have eq1 := Equation411_4512_implies_Equation1 G eq411 eq4512
  exact ⟨eq1, eq411, eq4512⟩

theorem AT54_implied_by_long (G : Type*) [Magma G] : AssociativeTheory54_long G -> AssociativeTheory54 G :=
fun ⟨_, h411, h4512⟩ => ⟨h411, h4512⟩

theorem AT54_equiv (G : Type*) [Magma G] : AssociativeTheory54 G <-> AssociativeTheory54_long G :=
Iff.intro (AT54_implies_long G) (AT54_implied_by_long G)

theorem AT55_implies_long (G : Type*) [Magma G] (h : AssociativeTheory55 G) : AssociativeTheory55_long G := by
  obtain ⟨eq43, eq411, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact ⟨eq1, eq43, eq411, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT55_implied_by_long (G : Type*) [Magma G] : AssociativeTheory55_long G -> AssociativeTheory55 G :=
fun ⟨_, h43, h411, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h411, h4512⟩

theorem AT55_equiv (G : Type*) [Magma G] : AssociativeTheory55 G <-> AssociativeTheory55_long G :=
Iff.intro (AT55_implies_long G) (AT55_implied_by_long G)

theorem AT56_implies_long (G : Type*) [Magma G] (h : AssociativeTheory56 G) : AssociativeTheory56_long G := by
  obtain ⟨eq419, eq4512⟩ := h
  have eq1 := Equation419_4512_implies_Equation1 G eq419 eq4512
  have eq8 := Equation419_4512_implies_Equation8 G eq419 eq4512
  have eq411 := Equation419_4512_implies_Equation411 G eq419 eq4512
  have eq429 := Equation419_4512_implies_Equation429 G eq419 eq4512
  have eq3253 := Equation419_4512_implies_Equation3253 G eq419 eq4512
  have eq3261 := Equation419_4512_implies_Equation3261 G eq419 eq4512
  have eq3306 := Equation419_4512_implies_Equation3306 G eq419 eq4512
  have eq3319 := Equation419_4512_implies_Equation3319 G eq419 eq4512
  have eq3334 := Equation419_4512_implies_Equation3334 G eq419 eq4512
  exact ⟨eq1, eq8, eq411, eq419, eq429, eq3253, eq3261, eq3306, eq3319, eq3334, eq4512⟩

theorem AT56_implied_by_long (G : Type*) [Magma G] : AssociativeTheory56_long G -> AssociativeTheory56 G :=
fun ⟨_, _, _, h419, _, _, _, _, _, _, h4512⟩ => ⟨h419, h4512⟩

theorem AT56_equiv (G : Type*) [Magma G] : AssociativeTheory56 G <-> AssociativeTheory56_long G :=
Iff.intro (AT56_implies_long G) (AT56_implied_by_long G)

theorem AT57_implies_long (G : Type*) [Magma G] (h : AssociativeTheory57 G) : AssociativeTheory57_long G := by
  obtain ⟨eq429, eq4512⟩ := h
  have eq1 := Equation429_4512_implies_Equation1 G eq429 eq4512
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  have eq411 := Equation429_4512_implies_Equation411 G eq429 eq4512
  have eq3253 := Equation429_4512_implies_Equation3253 G eq429 eq4512
  have eq3306 := Equation429_4512_implies_Equation3306 G eq429 eq4512
  have eq3319 := Equation429_4512_implies_Equation3319 G eq429 eq4512
  exact ⟨eq1, eq8, eq411, eq429, eq3253, eq3306, eq3319, eq4512⟩

theorem AT57_implied_by_long (G : Type*) [Magma G] : AssociativeTheory57_long G -> AssociativeTheory57 G :=
fun ⟨_, _, _, h429, _, _, _, h4512⟩ => ⟨h429, h4512⟩

theorem AT57_equiv (G : Type*) [Magma G] : AssociativeTheory57 G <-> AssociativeTheory57_long G :=
Iff.intro (AT57_implies_long G) (AT57_implied_by_long G)

theorem AT58_implies_long (G : Type*) [Magma G] (h : AssociativeTheory58 G) : AssociativeTheory58_long G := by
  obtain ⟨eq440, eq4512⟩ := h
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact ⟨eq1, eq411, eq440, eq4512⟩

theorem AT58_implied_by_long (G : Type*) [Magma G] : AssociativeTheory58_long G -> AssociativeTheory58 G :=
fun ⟨_, _, h440, h4512⟩ => ⟨h440, h4512⟩

theorem AT58_equiv (G : Type*) [Magma G] : AssociativeTheory58 G <-> AssociativeTheory58_long G :=
Iff.intro (AT58_implies_long G) (AT58_implied_by_long G)

theorem AT59_implies_long (G : Type*) [Magma G] (h : AssociativeTheory59 G) : AssociativeTheory59_long G := by
  obtain ⟨eq43, eq440, eq4512⟩ := h
  have eq477 := Equation43_440_4512_implies_Equation477 G eq43 eq440 eq4512
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq504 := Equation477_4512_implies_Equation504 G eq477 eq4512
  have eq513 := Equation477_4512_implies_Equation513 G eq477 eq4512
  exact ⟨eq1, eq43, eq411, eq440, eq477, eq504, eq513, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT59_implied_by_long (G : Type*) [Magma G] : AssociativeTheory59_long G -> AssociativeTheory59 G :=
fun ⟨_, h43, _, h440, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h440, h4512⟩

theorem AT59_equiv (G : Type*) [Magma G] : AssociativeTheory59 G <-> AssociativeTheory59_long G :=
Iff.intro (AT59_implies_long G) (AT59_implied_by_long G)

theorem AT60_implies_long (G : Type*) [Magma G] (h : AssociativeTheory60 G) : AssociativeTheory60_long G := by
  obtain ⟨eq504, eq4512⟩ := h
  have eq1 := Equation504_4512_implies_Equation1 G eq504 eq4512
  have eq411 := Equation504_4512_implies_Equation411 G eq504 eq4512
  have eq440 := Equation504_4512_implies_Equation440 G eq504 eq4512
  have eq513 := Equation504_4512_implies_Equation513 G eq504 eq4512
  have eq4290 := Equation504_4512_implies_Equation4290 G eq504 eq4512
  exact ⟨eq1, eq411, eq440, eq504, eq513, eq4290, eq4512⟩

theorem AT60_implied_by_long (G : Type*) [Magma G] : AssociativeTheory60_long G -> AssociativeTheory60 G :=
fun ⟨_, _, _, h504, _, _, h4512⟩ => ⟨h504, h4512⟩

theorem AT60_equiv (G : Type*) [Magma G] : AssociativeTheory60 G <-> AssociativeTheory60_long G :=
Iff.intro (AT60_implies_long G) (AT60_implied_by_long G)

theorem AT61_implies_long (G : Type*) [Magma G] (h : AssociativeTheory61 G) : AssociativeTheory61_long G := by
  obtain ⟨eq513, eq4512⟩ := h
  have eq1 := Equation513_4512_implies_Equation1 G eq513 eq4512
  have eq411 := Equation513_4512_implies_Equation411 G eq513 eq4512
  exact ⟨eq1, eq411, eq513, eq4512⟩

theorem AT61_implied_by_long (G : Type*) [Magma G] : AssociativeTheory61_long G -> AssociativeTheory61 G :=
fun ⟨_, _, h513, h4512⟩ => ⟨h513, h4512⟩

theorem AT61_equiv (G : Type*) [Magma G] : AssociativeTheory61 G <-> AssociativeTheory61_long G :=
Iff.intro (AT61_implies_long G) (AT61_implied_by_long G)

theorem AT62_implies_long (G : Type*) [Magma G] (h : AssociativeTheory62 G) : AssociativeTheory62_long G := by
  obtain ⟨eq440, eq513, eq4512⟩ := h
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact ⟨eq1, eq411, eq440, eq513, eq4512⟩

theorem AT62_implied_by_long (G : Type*) [Magma G] : AssociativeTheory62_long G -> AssociativeTheory62 G :=
fun ⟨_, _, h440, h513, h4512⟩ => ⟨h440, h513, h4512⟩

theorem AT62_equiv (G : Type*) [Magma G] : AssociativeTheory62 G <-> AssociativeTheory62_long G :=
Iff.intro (AT62_implies_long G) (AT62_implied_by_long G)

theorem AT63_implies_long (G : Type*) [Magma G] (h : AssociativeTheory63 G) : AssociativeTheory63_long G := by
  obtain ⟨eq3253, eq4512⟩ := h
  have eq1 := Equation3253_4512_implies_Equation1 G eq3253 eq4512
  exact ⟨eq1, eq3253, eq4512⟩

theorem AT63_implied_by_long (G : Type*) [Magma G] : AssociativeTheory63_long G -> AssociativeTheory63 G :=
fun ⟨_, h3253, h4512⟩ => ⟨h3253, h4512⟩

theorem AT63_equiv (G : Type*) [Magma G] : AssociativeTheory63 G <-> AssociativeTheory63_long G :=
Iff.intro (AT63_implies_long G) (AT63_implied_by_long G)

theorem AT64_implies_long (G : Type*) [Magma G] (h : AssociativeTheory64 G) : AssociativeTheory64_long G := by
  obtain ⟨eq43, eq3253, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact ⟨eq1, eq43, eq3253, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT64_implied_by_long (G : Type*) [Magma G] : AssociativeTheory64_long G -> AssociativeTheory64 G :=
fun ⟨_, h43, h3253, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h3253, h4512⟩

theorem AT64_equiv (G : Type*) [Magma G] : AssociativeTheory64 G <-> AssociativeTheory64_long G :=
Iff.intro (AT64_implies_long G) (AT64_implied_by_long G)

theorem AT65_implies_long (G : Type*) [Magma G] (h : AssociativeTheory65 G) : AssociativeTheory65_long G := by
  obtain ⟨eq3255, eq4512⟩ := h
  have eq1 := Equation3255_4512_implies_Equation1 G eq3255 eq4512
  have eq307 := Equation3255_4512_implies_Equation307 G eq3255 eq4512
  have eq3253 := Equation3255_4512_implies_Equation3253 G eq3255 eq4512
  exact ⟨eq1, eq307, eq3253, eq3255, eq4512⟩

theorem AT65_implied_by_long (G : Type*) [Magma G] : AssociativeTheory65_long G -> AssociativeTheory65 G :=
fun ⟨_, _, _, h3255, h4512⟩ => ⟨h3255, h4512⟩

theorem AT65_equiv (G : Type*) [Magma G] : AssociativeTheory65 G <-> AssociativeTheory65_long G :=
Iff.intro (AT65_implies_long G) (AT65_implied_by_long G)

theorem AT66_implies_long (G : Type*) [Magma G] (h : AssociativeTheory66 G) : AssociativeTheory66_long G := by
  obtain ⟨eq326, eq3255, eq4512⟩ := h
  have eq3322 := Equation326_3255_4512_implies_Equation3322 G eq326 eq3255 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3322_4512_implies_Equation307 G eq3322 eq4512
  have eq3253 := Equation3322_4512_implies_Equation3253 G eq3322 eq4512
  have eq3316 := Equation3322_4512_implies_Equation3316 G eq3322 eq4512
  have eq3319 := Equation3322_4512_implies_Equation3319 G eq3322 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3255, eq3316, eq3319, eq3322, eq4512⟩

theorem AT66_implied_by_long (G : Type*) [Magma G] : AssociativeTheory66_long G -> AssociativeTheory66 G :=
fun ⟨_, _, h326, _, h3255, _, _, _, h4512⟩ => ⟨h326, h3255, h4512⟩

theorem AT66_equiv (G : Type*) [Magma G] : AssociativeTheory66 G <-> AssociativeTheory66_long G :=
Iff.intro (AT66_implies_long G) (AT66_implied_by_long G)

theorem AT67_implies_long (G : Type*) [Magma G] (h : AssociativeTheory67 G) : AssociativeTheory67_long G := by
  obtain ⟨eq3256, eq4512⟩ := h
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  exact ⟨eq1, eq3253, eq3256, eq4512⟩

theorem AT67_implied_by_long (G : Type*) [Magma G] : AssociativeTheory67_long G -> AssociativeTheory67 G :=
fun ⟨_, _, h3256, h4512⟩ => ⟨h3256, h4512⟩

theorem AT67_equiv (G : Type*) [Magma G] : AssociativeTheory67 G <-> AssociativeTheory67_long G :=
Iff.intro (AT67_implies_long G) (AT67_implied_by_long G)

theorem AT68_implies_long (G : Type*) [Magma G] (h : AssociativeTheory68 G) : AssociativeTheory68_long G := by
  obtain ⟨eq3258, eq4512⟩ := h
  have eq1 := Equation3258_4512_implies_Equation1 G eq3258 eq4512
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation3258_4512_implies_Equation3253 G eq3258 eq4512
  exact ⟨eq1, eq307, eq3253, eq3258, eq4512⟩

theorem AT68_implied_by_long (G : Type*) [Magma G] : AssociativeTheory68_long G -> AssociativeTheory68 G :=
fun ⟨_, _, _, h3258, h4512⟩ => ⟨h3258, h4512⟩

theorem AT68_equiv (G : Type*) [Magma G] : AssociativeTheory68 G <-> AssociativeTheory68_long G :=
Iff.intro (AT68_implies_long G) (AT68_implied_by_long G)

theorem AT69_implies_long (G : Type*) [Magma G] (h : AssociativeTheory69 G) : AssociativeTheory69_long G := by
  obtain ⟨eq323, eq3258, eq4512⟩ := h
  have eq3326 := Equation323_3258_4512_implies_Equation3326 G eq323 eq3258 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation3258_4512_implies_Equation3253 G eq3258 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq3316 := Equation3326_4512_implies_Equation3316 G eq3326 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3258, eq3306, eq3316, eq3326, eq4512⟩

theorem AT69_implied_by_long (G : Type*) [Magma G] : AssociativeTheory69_long G -> AssociativeTheory69 G :=
fun ⟨_, _, h323, _, h3258, _, _, _, h4512⟩ => ⟨h323, h3258, h4512⟩

theorem AT69_equiv (G : Type*) [Magma G] : AssociativeTheory69 G <-> AssociativeTheory69_long G :=
Iff.intro (AT69_implies_long G) (AT69_implied_by_long G)

theorem AT70_implies_long (G : Type*) [Magma G] (h : AssociativeTheory70 G) : AssociativeTheory70_long G := by
  obtain ⟨eq3255, eq3258, eq4512⟩ := h
  have eq3261 := Equation3255_3258_4512_implies_Equation3261 G eq3255 eq3258 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation3258_4512_implies_Equation3253 G eq3258 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  exact ⟨eq1, eq307, eq3253, eq3255, eq3258, eq3261, eq4284, eq4512⟩

theorem AT70_implied_by_long (G : Type*) [Magma G] : AssociativeTheory70_long G -> AssociativeTheory70 G :=
fun ⟨_, _, _, h3255, h3258, _, _, h4512⟩ => ⟨h3255, h3258, h4512⟩

theorem AT70_equiv (G : Type*) [Magma G] : AssociativeTheory70 G <-> AssociativeTheory70_long G :=
Iff.intro (AT70_implies_long G) (AT70_implied_by_long G)

theorem AT71_implies_long (G : Type*) [Magma G] (h : AssociativeTheory71 G) : AssociativeTheory71_long G := by
  obtain ⟨eq3259, eq4512⟩ := h
  have eq1 := Equation3259_4512_implies_Equation1 G eq3259 eq4512
  have eq3253 := Equation3259_4512_implies_Equation3253 G eq3259 eq4512
  have eq3256 := Equation3259_4512_implies_Equation3256 G eq3259 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq4270, eq4512⟩

theorem AT71_implied_by_long (G : Type*) [Magma G] : AssociativeTheory71_long G -> AssociativeTheory71 G :=
fun ⟨_, _, _, h3259, _, _, h4512⟩ => ⟨h3259, h4512⟩

theorem AT71_equiv (G : Type*) [Magma G] : AssociativeTheory71 G <-> AssociativeTheory71_long G :=
Iff.intro (AT71_implies_long G) (AT71_implied_by_long G)

theorem AT72_implies_long (G : Type*) [Magma G] (h : AssociativeTheory72 G) : AssociativeTheory72_long G := by
  obtain ⟨eq3260, eq4512⟩ := h
  have eq1 := Equation3260_4512_implies_Equation1 G eq3260 eq4512
  have eq307 := Equation3260_4512_implies_Equation307 G eq3260 eq4512
  have eq308 := Equation3260_4512_implies_Equation308 G eq3260 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3253 := Equation3260_4512_implies_Equation3253 G eq3260 eq4512
  have eq3255 := Equation3260_4512_implies_Equation3255 G eq3260 eq4512
  have eq3256 := Equation3260_4512_implies_Equation3256 G eq3260 eq4512
  have eq3258 := Equation3260_4512_implies_Equation3258 G eq3260 eq4512
  have eq3259 := Equation3260_4512_implies_Equation3259 G eq3260 eq4512
  have eq3261 := Equation3260_4512_implies_Equation3261 G eq3260 eq4512
  have eq4268 := Equation3260_4512_implies_Equation4268 G eq3260 eq4512
  have eq4270 := Equation3260_4512_implies_Equation4270 G eq3260 eq4512
  have eq4284 := Equation3260_4512_implies_Equation4284 G eq3260 eq4512
  have eq4288 := Equation3260_4512_implies_Equation4288 G eq3260 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT72_implied_by_long (G : Type*) [Magma G] : AssociativeTheory72_long G -> AssociativeTheory72 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, _, _, _, _, h4512⟩ => ⟨h3260, h4512⟩

theorem AT72_equiv (G : Type*) [Magma G] : AssociativeTheory72 G <-> AssociativeTheory72_long G :=
Iff.intro (AT72_implies_long G) (AT72_implied_by_long G)

theorem AT73_implies_long (G : Type*) [Magma G] (h : AssociativeTheory73 G) : AssociativeTheory73_long G := by
  obtain ⟨eq40, eq3260, eq4512⟩ := h
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3273_4512_implies_Equation307 G eq3273 eq4512
  have eq308 := Equation3273_4512_implies_Equation308 G eq3273 eq4512
  have eq310 := Equation3273_4512_implies_Equation310 G eq3273 eq4512
  have eq312 := Equation3273_4512_implies_Equation312 G eq3273 eq4512
  have eq315 := Equation3273_4512_implies_Equation315 G eq3273 eq4512
  have eq316 := Equation3273_4512_implies_Equation316 G eq3273 eq4512
  have eq3255 := Equation3273_4512_implies_Equation3255 G eq3273 eq4512
  have eq3258 := Equation3273_4512_implies_Equation3258 G eq3273 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq4268 := Equation3273_4512_implies_Equation4268 G eq3273 eq4512
  have eq4272 := Equation3273_4512_implies_Equation4272 G eq3273 eq4512
  have eq4276 := Equation3273_4512_implies_Equation4276 G eq3273 eq4512
  have eq4277 := Equation3273_4512_implies_Equation4277 G eq3273 eq4512
  have eq4280 := Equation3273_4512_implies_Equation4280 G eq3273 eq4512
  have eq4284 := Equation3273_4512_implies_Equation4284 G eq3273 eq4512
  have eq4288 := Equation3273_4512_implies_Equation4288 G eq3273 eq4512
  have eq4293 := Equation3273_4512_implies_Equation4293 G eq3273 eq4512
  have eq4299 := Equation3273_4512_implies_Equation4299 G eq3273 eq4512
  have eq4304 := Equation3273_4512_implies_Equation4304 G eq3273 eq4512
  have eq4343 := Equation3273_4512_implies_Equation4343 G eq3273 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3271, eq3273, eq3278, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT73_implied_by_long (G : Type*) [Magma G] : AssociativeTheory73_long G -> AssociativeTheory73 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h4512⟩

theorem AT73_equiv (G : Type*) [Magma G] : AssociativeTheory73 G <-> AssociativeTheory73_long G :=
Iff.intro (AT73_implies_long G) (AT73_implied_by_long G)

theorem AT74_implies_long (G : Type*) [Magma G] (h : AssociativeTheory74 G) : AssociativeTheory74_long G := by
  obtain ⟨eq3261, eq4512⟩ := h
  have eq1 := Equation3261_4512_implies_Equation1 G eq3261 eq4512
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  exact ⟨eq1, eq3253, eq3261, eq4512⟩

theorem AT74_implied_by_long (G : Type*) [Magma G] : AssociativeTheory74_long G -> AssociativeTheory74 G :=
fun ⟨_, _, h3261, h4512⟩ => ⟨h3261, h4512⟩

theorem AT74_equiv (G : Type*) [Magma G] : AssociativeTheory74 G <-> AssociativeTheory74_long G :=
Iff.intro (AT74_implies_long G) (AT74_implied_by_long G)

theorem AT75_implies_long (G : Type*) [Magma G] (h : AssociativeTheory75 G) : AssociativeTheory75_long G := by
  obtain ⟨eq3264, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact ⟨eq1, eq307, eq3253, eq3255, eq3258, eq3261, eq3264, eq4284, eq4512⟩

theorem AT75_implied_by_long (G : Type*) [Magma G] : AssociativeTheory75_long G -> AssociativeTheory75 G :=
fun ⟨_, _, _, _, _, _, h3264, _, h4512⟩ => ⟨h3264, h4512⟩

theorem AT75_equiv (G : Type*) [Magma G] : AssociativeTheory75 G <-> AssociativeTheory75_long G :=
Iff.intro (AT75_implies_long G) (AT75_implied_by_long G)

theorem AT76_implies_long (G : Type*) [Magma G] (h : AssociativeTheory76 G) : AssociativeTheory76_long G := by
  obtain ⟨eq40, eq3264, eq4512⟩ := h
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3275_4512_implies_Equation307 G eq3275 eq4512
  have eq308 := Equation3275_4512_implies_Equation308 G eq3275 eq4512
  have eq310 := Equation3275_4512_implies_Equation310 G eq3275 eq4512
  have eq312 := Equation3275_4512_implies_Equation312 G eq3275 eq4512
  have eq315 := Equation3275_4512_implies_Equation315 G eq3275 eq4512
  have eq316 := Equation3275_4512_implies_Equation316 G eq3275 eq4512
  have eq3255 := Equation3275_4512_implies_Equation3255 G eq3275 eq4512
  have eq3258 := Equation3275_4512_implies_Equation3258 G eq3275 eq4512
  have eq4268 := Equation3275_4512_implies_Equation4268 G eq3275 eq4512
  have eq4272 := Equation3275_4512_implies_Equation4272 G eq3275 eq4512
  have eq4276 := Equation3275_4512_implies_Equation4276 G eq3275 eq4512
  have eq4277 := Equation3275_4512_implies_Equation4277 G eq3275 eq4512
  have eq4280 := Equation3275_4512_implies_Equation4280 G eq3275 eq4512
  have eq4284 := Equation3275_4512_implies_Equation4284 G eq3275 eq4512
  have eq4288 := Equation3275_4512_implies_Equation4288 G eq3275 eq4512
  have eq4293 := Equation3275_4512_implies_Equation4293 G eq3275 eq4512
  have eq4299 := Equation3275_4512_implies_Equation4299 G eq3275 eq4512
  have eq4304 := Equation3275_4512_implies_Equation4304 G eq3275 eq4512
  have eq4343 := Equation3275_4512_implies_Equation4343 G eq3275 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3264, eq3271, eq3275, eq3278, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT76_implied_by_long (G : Type*) [Magma G] : AssociativeTheory76_long G -> AssociativeTheory76 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, h3264, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3264, h4512⟩

theorem AT76_equiv (G : Type*) [Magma G] : AssociativeTheory76 G <-> AssociativeTheory76_long G :=
Iff.intro (AT76_implies_long G) (AT76_implied_by_long G)

theorem AT77_implies_long (G : Type*) [Magma G] (h : AssociativeTheory77 G) : AssociativeTheory77_long G := by
  obtain ⟨eq308, eq3264, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  have eq4270 := Equation4268_4284_4512_implies_Equation4270 G eq4268 eq4284 eq4512
  have eq310 := Equation308_4284_4512_implies_Equation310 G eq308 eq4284 eq4512
  have eq3259 := Equation3256_3261_4512_implies_Equation3259 G eq3256 eq3261 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3264, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT77_implied_by_long (G : Type*) [Magma G] : AssociativeTheory77_long G -> AssociativeTheory77 G :=
fun ⟨_, _, h308, _, _, _, _, _, _, _, h3264, _, _, _, _, h4512⟩ => ⟨h308, h3264, h4512⟩

theorem AT77_equiv (G : Type*) [Magma G] : AssociativeTheory77 G <-> AssociativeTheory77_long G :=
Iff.intro (AT77_implies_long G) (AT77_implied_by_long G)

theorem AT78_implies_long (G : Type*) [Magma G] (h : AssociativeTheory78 G) : AssociativeTheory78_long G := by
  obtain ⟨eq312, eq3264, eq4512⟩ := h
  have eq1 := Equation312_4512_implies_Equation1 G eq312 eq4512
  have eq307 := Equation312_4512_implies_Equation307 G eq312 eq4512
  have eq3253 := Equation312_4512_implies_Equation3253 G eq312 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq4275 := Equation4272_4284_4512_implies_Equation4275 G eq4272 eq4284 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq3271 := Equation3261_3278_4512_implies_Equation3271 G eq3261 eq3278 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3278, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT78_implied_by_long (G : Type*) [Magma G] : AssociativeTheory78_long G -> AssociativeTheory78 G :=
fun ⟨_, _, h312, _, _, _, _, _, h3264, _, _, _, _, _, _, h4512⟩ => ⟨h312, h3264, h4512⟩

theorem AT78_equiv (G : Type*) [Magma G] : AssociativeTheory78 G <-> AssociativeTheory78_long G :=
Iff.intro (AT78_implies_long G) (AT78_implied_by_long G)

theorem AT79_implies_long (G : Type*) [Magma G] (h : AssociativeTheory79 G) : AssociativeTheory79_long G := by
  obtain ⟨eq3260, eq3264, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq308 := Equation3260_4512_implies_Equation308 G eq3260 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3256 := Equation3260_4512_implies_Equation3256 G eq3260 eq4512
  have eq3259 := Equation3260_4512_implies_Equation3259 G eq3260 eq4512
  have eq4268 := Equation3260_4512_implies_Equation4268 G eq3260 eq4512
  have eq4270 := Equation3260_4512_implies_Equation4270 G eq3260 eq4512
  have eq4288 := Equation3260_4512_implies_Equation4288 G eq3260 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT79_implied_by_long (G : Type*) [Magma G] : AssociativeTheory79_long G -> AssociativeTheory79 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, h3264, _, _, _, _, h4512⟩ => ⟨h3260, h3264, h4512⟩

theorem AT79_equiv (G : Type*) [Magma G] : AssociativeTheory79 G <-> AssociativeTheory79_long G :=
Iff.intro (AT79_implies_long G) (AT79_implied_by_long G)

theorem AT80_implies_long (G : Type*) [Magma G] (h : AssociativeTheory80 G) : AssociativeTheory80_long G := by
  obtain ⟨eq40, eq3260, eq3264, eq4512⟩ := h
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3260_4512_implies_Equation307 G eq3260 eq4512
  have eq308 := Equation3260_4512_implies_Equation308 G eq3260 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3255 := Equation3260_4512_implies_Equation3255 G eq3260 eq4512
  have eq3258 := Equation3260_4512_implies_Equation3258 G eq3260 eq4512
  have eq4268 := Equation3260_4512_implies_Equation4268 G eq3260 eq4512
  have eq4284 := Equation3260_4512_implies_Equation4284 G eq3260 eq4512
  have eq4288 := Equation3260_4512_implies_Equation4288 G eq3260 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq315 := Equation3273_4512_implies_Equation315 G eq3273 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq4276 := Equation3273_4512_implies_Equation4276 G eq3273 eq4512
  have eq4280 := Equation3273_4512_implies_Equation4280 G eq3273 eq4512
  have eq4299 := Equation3273_4512_implies_Equation4299 G eq3273 eq4512
  have eq4304 := Equation3273_4512_implies_Equation4304 G eq3273 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3271, eq3273, eq3275, eq3278, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT80_implied_by_long (G : Type*) [Magma G] : AssociativeTheory80_long G -> AssociativeTheory80 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, h3264, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h3264, h4512⟩

theorem AT80_equiv (G : Type*) [Magma G] : AssociativeTheory80 G <-> AssociativeTheory80_long G :=
Iff.intro (AT80_implies_long G) (AT80_implied_by_long G)

theorem AT81_implies_long (G : Type*) [Magma G] (h : AssociativeTheory81 G) : AssociativeTheory81_long G := by
  obtain ⟨eq3265, eq4512⟩ := h
  have eq1 := Equation3265_4512_implies_Equation1 G eq3265 eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3253 := Equation3265_4512_implies_Equation3253 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq3261 := Equation3265_4512_implies_Equation3261 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3265, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT81_implied_by_long (G : Type*) [Magma G] : AssociativeTheory81_long G -> AssociativeTheory81 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, h3265, _, _, _, _, h4512⟩ => ⟨h3265, h4512⟩

theorem AT81_equiv (G : Type*) [Magma G] : AssociativeTheory81 G <-> AssociativeTheory81_long G :=
Iff.intro (AT81_implies_long G) (AT81_implied_by_long G)

theorem AT82_implies_long (G : Type*) [Magma G] (h : AssociativeTheory82 G) : AssociativeTheory82_long G := by
  obtain ⟨eq40, eq3265, eq4512⟩ := h
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq312 := Equation3290_4512_implies_Equation312 G eq3290 eq4512
  have eq315 := Equation3290_4512_implies_Equation315 G eq3290 eq4512
  have eq316 := Equation3290_4512_implies_Equation316 G eq3290 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  have eq4272 := Equation3290_4512_implies_Equation4272 G eq3290 eq4512
  have eq4276 := Equation3290_4512_implies_Equation4276 G eq3290 eq4512
  have eq4277 := Equation3290_4512_implies_Equation4277 G eq3290 eq4512
  have eq4280 := Equation3290_4512_implies_Equation4280 G eq3290 eq4512
  have eq4293 := Equation3290_4512_implies_Equation4293 G eq3290 eq4512
  have eq4299 := Equation3290_4512_implies_Equation4299 G eq3290 eq4512
  have eq4304 := Equation3290_4512_implies_Equation4304 G eq3290 eq4512
  have eq4343 := Equation3290_4512_implies_Equation4343 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3265, eq3271, eq3274, eq3278, eq3290, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT82_implied_by_long (G : Type*) [Magma G] : AssociativeTheory82_long G -> AssociativeTheory82 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3265, h4512⟩

theorem AT82_equiv (G : Type*) [Magma G] : AssociativeTheory82 G <-> AssociativeTheory82_long G :=
Iff.intro (AT82_implies_long G) (AT82_implied_by_long G)

theorem AT83_implies_long (G : Type*) [Magma G] (h : AssociativeTheory83 G) : AssociativeTheory83_long G := by
  obtain ⟨eq3260, eq3265, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3253 := Equation3265_4512_implies_Equation3253 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq3261 := Equation3265_4512_implies_Equation3261 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3265, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT83_implied_by_long (G : Type*) [Magma G] : AssociativeTheory83_long G -> AssociativeTheory83 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, h3265, _, _, _, _, h4512⟩ => ⟨h3260, h3265, h4512⟩

theorem AT83_equiv (G : Type*) [Magma G] : AssociativeTheory83 G <-> AssociativeTheory83_long G :=
Iff.intro (AT83_implies_long G) (AT83_implied_by_long G)

theorem AT84_implies_long (G : Type*) [Magma G] (h : AssociativeTheory84 G) : AssociativeTheory84_long G := by
  obtain ⟨eq40, eq3260, eq3265, eq4512⟩ := h
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq315 := Equation3273_4512_implies_Equation315 G eq3273 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq4276 := Equation3273_4512_implies_Equation4276 G eq3273 eq4512
  have eq4280 := Equation3273_4512_implies_Equation4280 G eq3273 eq4512
  have eq4299 := Equation3273_4512_implies_Equation4299 G eq3273 eq4512
  have eq4304 := Equation3273_4512_implies_Equation4304 G eq3273 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3265, eq3271, eq3273, eq3274, eq3278, eq3290, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT84_implied_by_long (G : Type*) [Magma G] : AssociativeTheory84_long G -> AssociativeTheory84 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h3265, h4512⟩

theorem AT84_equiv (G : Type*) [Magma G] : AssociativeTheory84 G <-> AssociativeTheory84_long G :=
Iff.intro (AT84_implies_long G) (AT84_implied_by_long G)

theorem AT85_implies_long (G : Type*) [Magma G] (h : AssociativeTheory85 G) : AssociativeTheory85_long G := by
  obtain ⟨eq3264, eq3265, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3264, eq3265, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT85_implied_by_long (G : Type*) [Magma G] : AssociativeTheory85_long G -> AssociativeTheory85 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, h3264, h3265, _, _, _, _, h4512⟩ => ⟨h3264, h3265, h4512⟩

theorem AT85_equiv (G : Type*) [Magma G] : AssociativeTheory85 G <-> AssociativeTheory85_long G :=
Iff.intro (AT85_implies_long G) (AT85_implied_by_long G)

theorem AT86_implies_long (G : Type*) [Magma G] (h : AssociativeTheory86 G) : AssociativeTheory86_long G := by
  obtain ⟨eq40, eq3264, eq3265, eq4512⟩ := h
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq315 := Equation3275_4512_implies_Equation315 G eq3275 eq4512
  have eq4276 := Equation3275_4512_implies_Equation4276 G eq3275 eq4512
  have eq4280 := Equation3275_4512_implies_Equation4280 G eq3275 eq4512
  have eq4299 := Equation3275_4512_implies_Equation4299 G eq3275 eq4512
  have eq4304 := Equation3275_4512_implies_Equation4304 G eq3275 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3264, eq3265, eq3271, eq3274, eq3275, eq3278, eq3290, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT86_implied_by_long (G : Type*) [Magma G] : AssociativeTheory86_long G -> AssociativeTheory86 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, h3264, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3264, h3265, h4512⟩

theorem AT86_equiv (G : Type*) [Magma G] : AssociativeTheory86 G <-> AssociativeTheory86_long G :=
Iff.intro (AT86_implies_long G) (AT86_implied_by_long G)

theorem AT87_implies_long (G : Type*) [Magma G] (h : AssociativeTheory87 G) : AssociativeTheory87_long G := by
  obtain ⟨eq3260, eq3264, eq3265, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT87_implied_by_long (G : Type*) [Magma G] : AssociativeTheory87_long G -> AssociativeTheory87 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, h3264, h3265, _, _, _, _, h4512⟩ => ⟨h3260, h3264, h3265, h4512⟩

theorem AT87_equiv (G : Type*) [Magma G] : AssociativeTheory87 G <-> AssociativeTheory87_long G :=
Iff.intro (AT87_implies_long G) (AT87_implied_by_long G)

theorem AT88_implies_long (G : Type*) [Magma G] (h : AssociativeTheory88 G) : AssociativeTheory88_long G := by
  obtain ⟨eq40, eq3260, eq3264, eq3265, eq4512⟩ := h
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3253 := Equation3265_4512_implies_Equation3253 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq3261 := Equation3265_4512_implies_Equation3261 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq315 := Equation3273_4512_implies_Equation315 G eq3273 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq4276 := Equation3273_4512_implies_Equation4276 G eq3273 eq4512
  have eq4280 := Equation3273_4512_implies_Equation4280 G eq3273 eq4512
  have eq4299 := Equation3273_4512_implies_Equation4299 G eq3273 eq4512
  have eq4304 := Equation3273_4512_implies_Equation4304 G eq3273 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT88_implied_by_long (G : Type*) [Magma G] : AssociativeTheory88_long G -> AssociativeTheory88 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, h3264, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h3264, h3265, h4512⟩

theorem AT88_equiv (G : Type*) [Magma G] : AssociativeTheory88 G <-> AssociativeTheory88_long G :=
Iff.intro (AT88_implies_long G) (AT88_implied_by_long G)

theorem AT89_implies_long (G : Type*) [Magma G] (h : AssociativeTheory89 G) : AssociativeTheory89_long G := by
  obtain ⟨eq3267, eq4512⟩ := h
  have eq1 := Equation3267_4512_implies_Equation1 G eq3267 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  exact ⟨eq1, eq307, eq308, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT89_implied_by_long (G : Type*) [Magma G] : AssociativeTheory89_long G -> AssociativeTheory89 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, h4512⟩ => ⟨h3267, h4512⟩

theorem AT89_equiv (G : Type*) [Magma G] : AssociativeTheory89 G <-> AssociativeTheory89_long G :=
Iff.intro (AT89_implies_long G) (AT89_implied_by_long G)

theorem AT90_implies_long (G : Type*) [Magma G] (h : AssociativeTheory90 G) : AssociativeTheory90_long G := by
  obtain ⟨eq40, eq3267, eq4512⟩ := h
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq312 := Equation3277_4512_implies_Equation312 G eq3277 eq4512
  have eq315 := Equation3277_4512_implies_Equation315 G eq3277 eq4512
  have eq316 := Equation3277_4512_implies_Equation316 G eq3277 eq4512
  have eq3273 := Equation3277_4512_implies_Equation3273 G eq3277 eq4512
  have eq3274 := Equation3277_4512_implies_Equation3274 G eq3277 eq4512
  have eq3275 := Equation3277_4512_implies_Equation3275 G eq3277 eq4512
  have eq3290 := Equation3277_4512_implies_Equation3290 G eq3277 eq4512
  have eq3292 := Equation3277_4512_implies_Equation3292 G eq3277 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq4272 := Equation3277_4512_implies_Equation4272 G eq3277 eq4512
  have eq4276 := Equation3277_4512_implies_Equation4276 G eq3277 eq4512
  have eq4277 := Equation3277_4512_implies_Equation4277 G eq3277 eq4512
  have eq4280 := Equation3277_4512_implies_Equation4280 G eq3277 eq4512
  have eq4293 := Equation3277_4512_implies_Equation4293 G eq3277 eq4512
  have eq4299 := Equation3277_4512_implies_Equation4299 G eq3277 eq4512
  have eq4304 := Equation3277_4512_implies_Equation4304 G eq3277 eq4512
  have eq4343 := Equation3277_4512_implies_Equation4343 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT90_implied_by_long (G : Type*) [Magma G] : AssociativeTheory90_long G -> AssociativeTheory90 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3267, h4512⟩

theorem AT90_equiv (G : Type*) [Magma G] : AssociativeTheory90 G <-> AssociativeTheory90_long G :=
Iff.intro (AT90_implies_long G) (AT90_implied_by_long G)

theorem AT91_implies_long (G : Type*) [Magma G] (h : AssociativeTheory91 G) : AssociativeTheory91_long G := by
  obtain ⟨eq43, eq3267, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq40 := Equation3255_4290_4512_implies_Equation40 G eq3255 eq4290 eq4512
  have eq309 := Equation3255_4320_4512_implies_Equation309 G eq3255 eq4320 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq43, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT91_implied_by_long (G : Type*) [Magma G] : AssociativeTheory91_long G -> AssociativeTheory91 G :=
fun ⟨_, _, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h3267, h4512⟩

theorem AT91_equiv (G : Type*) [Magma G] : AssociativeTheory91 G <-> AssociativeTheory91_long G :=
Iff.intro (AT91_implies_long G) (AT91_implied_by_long G)

theorem AT92_implies_long (G : Type*) [Magma G] (h : AssociativeTheory92 G) : AssociativeTheory92_long G := by
  obtain ⟨eq309, eq3267, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact ⟨eq1, eq307, eq308, eq309, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4512⟩

theorem AT92_implied_by_long (G : Type*) [Magma G] : AssociativeTheory92_long G -> AssociativeTheory92 G :=
fun ⟨_, _, _, h309, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h3267, h4512⟩

theorem AT92_equiv (G : Type*) [Magma G] : AssociativeTheory92 G <-> AssociativeTheory92_long G :=
Iff.intro (AT92_implies_long G) (AT92_implied_by_long G)

theorem AT93_implies_long (G : Type*) [Magma G] (h : AssociativeTheory93 G) : AssociativeTheory93_long G := by
  obtain ⟨eq40, eq309, eq3267, eq4512⟩ := h
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq315 := Equation3277_4512_implies_Equation315 G eq3277 eq4512
  have eq3274 := Equation3277_4512_implies_Equation3274 G eq3277 eq4512
  have eq3292 := Equation3277_4512_implies_Equation3292 G eq3277 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq4276 := Equation3277_4512_implies_Equation4276 G eq3277 eq4512
  have eq4280 := Equation3277_4512_implies_Equation4280 G eq3277 eq4512
  have eq4299 := Equation3277_4512_implies_Equation4299 G eq3277 eq4512
  have eq4304 := Equation3277_4512_implies_Equation4304 G eq3277 eq4512
  have eq4279 := Equation313_4512_implies_Equation4279 G eq313 eq4512
  have eq4283 := Equation313_4512_implies_Equation4283 G eq313 eq4512
  have eq4291 := Equation313_4512_implies_Equation4291 G eq313 eq4512
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4305 := Equation313_4512_implies_Equation4305 G eq313 eq4512
  have eq4314 := Equation313_4512_implies_Equation4314 G eq313 eq4512
  have eq4320 := Equation313_4512_implies_Equation4320 G eq313 eq4512
  have eq4321 := Equation313_4512_implies_Equation4321 G eq313 eq4512
  have eq4325 := Equation313_4512_implies_Equation4325 G eq313 eq4512
  have eq4327 := Equation313_4512_implies_Equation4327 G eq313 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4512⟩

theorem AT93_implied_by_long (G : Type*) [Magma G] : AssociativeTheory93_long G -> AssociativeTheory93 G :=
fun ⟨_, h40, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h309, h3267, h4512⟩

theorem AT93_equiv (G : Type*) [Magma G] : AssociativeTheory93 G <-> AssociativeTheory93_long G :=
Iff.intro (AT93_implies_long G) (AT93_implied_by_long G)

theorem AT94_implies_long (G : Type*) [Magma G] (h : AssociativeTheory94 G) : AssociativeTheory94_long G := by
  obtain ⟨eq3271, eq4512⟩ := h
  have eq1 := Equation3271_4512_implies_Equation1 G eq3271 eq4512
  have eq3253 := Equation3271_4512_implies_Equation3253 G eq3271 eq4512
  have eq3261 := Equation3271_4512_implies_Equation3261 G eq3271 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq4275, eq4512⟩

theorem AT94_implied_by_long (G : Type*) [Magma G] : AssociativeTheory94_long G -> AssociativeTheory94 G :=
fun ⟨_, _, _, h3271, _, _, h4512⟩ => ⟨h3271, h4512⟩

theorem AT94_equiv (G : Type*) [Magma G] : AssociativeTheory94 G <-> AssociativeTheory94_long G :=
Iff.intro (AT94_implies_long G) (AT94_implied_by_long G)

theorem AT95_implies_long (G : Type*) [Magma G] (h : AssociativeTheory95 G) : AssociativeTheory95_long G := by
  obtain ⟨eq3274, eq4512⟩ := h
  have eq1 := Equation3274_4512_implies_Equation1 G eq3274 eq4512
  have eq307 := Equation3274_4512_implies_Equation307 G eq3274 eq4512
  have eq312 := Equation3274_4512_implies_Equation312 G eq3274 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3253 := Equation3274_4512_implies_Equation3253 G eq3274 eq4512
  have eq3255 := Equation3274_4512_implies_Equation3255 G eq3274 eq4512
  have eq3258 := Equation3274_4512_implies_Equation3258 G eq3274 eq4512
  have eq3261 := Equation3274_4512_implies_Equation3261 G eq3274 eq4512
  have eq3271 := Equation3274_4512_implies_Equation3271 G eq3274 eq4512
  have eq3278 := Equation3274_4512_implies_Equation3278 G eq3274 eq4512
  have eq4272 := Equation3274_4512_implies_Equation4272 G eq3274 eq4512
  have eq4275 := Equation3274_4512_implies_Equation4275 G eq3274 eq4512
  have eq4284 := Equation3274_4512_implies_Equation4284 G eq3274 eq4512
  have eq4304 := Equation3274_4512_implies_Equation4304 G eq3274 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3271, eq3274, eq3278, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT95_implied_by_long (G : Type*) [Magma G] : AssociativeTheory95_long G -> AssociativeTheory95 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3274, _, _, _, _, _, h4512⟩ => ⟨h3274, h4512⟩

theorem AT95_equiv (G : Type*) [Magma G] : AssociativeTheory95 G <-> AssociativeTheory95_long G :=
Iff.intro (AT95_implies_long G) (AT95_implied_by_long G)

theorem AT96_implies_long (G : Type*) [Magma G] (h : AssociativeTheory96 G) : AssociativeTheory96_long G := by
  obtain ⟨eq3264, eq3274, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq312 := Equation3274_4512_implies_Equation312 G eq3274 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation3274_4512_implies_Equation3271 G eq3274 eq4512
  have eq3278 := Equation3274_4512_implies_Equation3278 G eq3274 eq4512
  have eq4272 := Equation3274_4512_implies_Equation4272 G eq3274 eq4512
  have eq4275 := Equation3274_4512_implies_Equation4275 G eq3274 eq4512
  have eq4304 := Equation3274_4512_implies_Equation4304 G eq3274 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT96_implied_by_long (G : Type*) [Magma G] : AssociativeTheory96_long G -> AssociativeTheory96 G :=
fun ⟨_, _, _, _, _, _, _, _, h3264, _, h3274, _, _, _, _, _, h4512⟩ => ⟨h3264, h3274, h4512⟩

theorem AT96_equiv (G : Type*) [Magma G] : AssociativeTheory96 G <-> AssociativeTheory96_long G :=
Iff.intro (AT96_implies_long G) (AT96_implied_by_long G)

theorem AT97_implies_long (G : Type*) [Magma G] (h : AssociativeTheory97 G) : AssociativeTheory97_long G := by
  obtain ⟨eq3278, eq4512⟩ := h
  have eq1 := Equation3278_4512_implies_Equation1 G eq3278 eq4512
  have eq3253 := Equation3278_4512_implies_Equation3253 G eq3278 eq4512
  exact ⟨eq1, eq3253, eq3278, eq4512⟩

theorem AT97_implied_by_long (G : Type*) [Magma G] : AssociativeTheory97_long G -> AssociativeTheory97 G :=
fun ⟨_, _, h3278, h4512⟩ => ⟨h3278, h4512⟩

theorem AT97_equiv (G : Type*) [Magma G] : AssociativeTheory97 G <-> AssociativeTheory97_long G :=
Iff.intro (AT97_implies_long G) (AT97_implied_by_long G)

theorem AT98_implies_long (G : Type*) [Magma G] (h : AssociativeTheory98 G) : AssociativeTheory98_long G := by
  obtain ⟨eq3292, eq4512⟩ := h
  have eq1 := Equation3292_4512_implies_Equation1 G eq3292 eq4512
  have eq307 := Equation3292_4512_implies_Equation307 G eq3292 eq4512
  have eq312 := Equation3292_4512_implies_Equation312 G eq3292 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3253 := Equation3292_4512_implies_Equation3253 G eq3292 eq4512
  have eq3255 := Equation3292_4512_implies_Equation3255 G eq3292 eq4512
  have eq3258 := Equation3292_4512_implies_Equation3258 G eq3292 eq4512
  have eq3261 := Equation3292_4512_implies_Equation3261 G eq3292 eq4512
  have eq3271 := Equation3292_4512_implies_Equation3271 G eq3292 eq4512
  have eq3278 := Equation3292_4512_implies_Equation3278 G eq3292 eq4512
  have eq4272 := Equation3292_4512_implies_Equation4272 G eq3292 eq4512
  have eq4275 := Equation3292_4512_implies_Equation4275 G eq3292 eq4512
  have eq4284 := Equation3292_4512_implies_Equation4284 G eq3292 eq4512
  have eq4304 := Equation3292_4512_implies_Equation4304 G eq3292 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3271, eq3278, eq3292, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT98_implied_by_long (G : Type*) [Magma G] : AssociativeTheory98_long G -> AssociativeTheory98 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, h3292, _, _, _, _, h4512⟩ => ⟨h3292, h4512⟩

theorem AT98_equiv (G : Type*) [Magma G] : AssociativeTheory98 G <-> AssociativeTheory98_long G :=
Iff.intro (AT98_implies_long G) (AT98_implied_by_long G)

theorem AT99_implies_long (G : Type*) [Magma G] (h : AssociativeTheory99 G) : AssociativeTheory99_long G := by
  obtain ⟨eq3264, eq3292, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq312 := Equation3292_4512_implies_Equation312 G eq3292 eq4512
  have eq315 := Equation3292_4512_implies_Equation315 G eq3292 eq4512
  have eq3271 := Equation3292_4512_implies_Equation3271 G eq3292 eq4512
  have eq3278 := Equation3292_4512_implies_Equation3278 G eq3292 eq4512
  have eq4272 := Equation3292_4512_implies_Equation4272 G eq3292 eq4512
  have eq4275 := Equation3292_4512_implies_Equation4275 G eq3292 eq4512
  have eq4304 := Equation3292_4512_implies_Equation4304 G eq3292 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3278, eq3292, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT99_implied_by_long (G : Type*) [Magma G] : AssociativeTheory99_long G -> AssociativeTheory99 G :=
fun ⟨_, _, _, _, _, _, _, _, h3264, _, _, h3292, _, _, _, _, h4512⟩ => ⟨h3264, h3292, h4512⟩

theorem AT99_equiv (G : Type*) [Magma G] : AssociativeTheory99 G <-> AssociativeTheory99_long G :=
Iff.intro (AT99_implies_long G) (AT99_implied_by_long G)

theorem AT100_implies_long (G : Type*) [Magma G] (h : AssociativeTheory100 G) : AssociativeTheory100_long G := by
  obtain ⟨eq3274, eq3292, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3274_4512_implies_Equation307 G eq3274 eq4512
  have eq312 := Equation3274_4512_implies_Equation312 G eq3274 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3253 := Equation3274_4512_implies_Equation3253 G eq3274 eq4512
  have eq3255 := Equation3274_4512_implies_Equation3255 G eq3274 eq4512
  have eq3258 := Equation3274_4512_implies_Equation3258 G eq3274 eq4512
  have eq3261 := Equation3274_4512_implies_Equation3261 G eq3274 eq4512
  have eq3271 := Equation3274_4512_implies_Equation3271 G eq3274 eq4512
  have eq3278 := Equation3274_4512_implies_Equation3278 G eq3274 eq4512
  have eq4272 := Equation3274_4512_implies_Equation4272 G eq3274 eq4512
  have eq4275 := Equation3274_4512_implies_Equation4275 G eq3274 eq4512
  have eq4284 := Equation3274_4512_implies_Equation4284 G eq3274 eq4512
  have eq4304 := Equation3274_4512_implies_Equation4304 G eq3274 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3271, eq3274, eq3278, eq3292, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT100_implied_by_long (G : Type*) [Magma G] : AssociativeTheory100_long G -> AssociativeTheory100 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3274, _, h3292, _, _, _, _, h4512⟩ => ⟨h3274, h3292, h4512⟩

theorem AT100_equiv (G : Type*) [Magma G] : AssociativeTheory100 G <-> AssociativeTheory100_long G :=
Iff.intro (AT100_implies_long G) (AT100_implied_by_long G)

theorem AT101_implies_long (G : Type*) [Magma G] (h : AssociativeTheory101 G) : AssociativeTheory101_long G := by
  obtain ⟨eq3264, eq3274, eq3292, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq312 := Equation3274_4512_implies_Equation312 G eq3274 eq4512
  have eq315 := Equation3274_4512_implies_Equation315 G eq3274 eq4512
  have eq3271 := Equation3274_4512_implies_Equation3271 G eq3274 eq4512
  have eq3278 := Equation3274_4512_implies_Equation3278 G eq3274 eq4512
  have eq4272 := Equation3274_4512_implies_Equation4272 G eq3274 eq4512
  have eq4275 := Equation3274_4512_implies_Equation4275 G eq3274 eq4512
  have eq4304 := Equation3274_4512_implies_Equation4304 G eq3274 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT101_implied_by_long (G : Type*) [Magma G] : AssociativeTheory101_long G -> AssociativeTheory101 G :=
fun ⟨_, _, _, _, _, _, _, _, h3264, _, h3274, _, h3292, _, _, _, _, h4512⟩ => ⟨h3264, h3274, h3292, h4512⟩

theorem AT101_equiv (G : Type*) [Magma G] : AssociativeTheory101 G <-> AssociativeTheory101_long G :=
Iff.intro (AT101_implies_long G) (AT101_implied_by_long G)

theorem AT102_implies_long (G : Type*) [Magma G] (h : AssociativeTheory102 G) : AssociativeTheory102_long G := by
  obtain ⟨eq3300, eq4512⟩ := h
  have eq1 := Equation3300_4512_implies_Equation1 G eq3300 eq4512
  have eq307 := Equation3300_4512_implies_Equation307 G eq3300 eq4512
  have eq312 := Equation3300_4512_implies_Equation312 G eq3300 eq4512
  have eq315 := Equation3300_4512_implies_Equation315 G eq3300 eq4512
  have eq3253 := Equation3300_4512_implies_Equation3253 G eq3300 eq4512
  have eq3255 := Equation3300_4512_implies_Equation3255 G eq3300 eq4512
  have eq3258 := Equation3300_4512_implies_Equation3258 G eq3300 eq4512
  have eq3261 := Equation3300_4512_implies_Equation3261 G eq3300 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq3271 := Equation3300_4512_implies_Equation3271 G eq3300 eq4512
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq3278 := Equation3300_4512_implies_Equation3278 G eq3300 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq4272 := Equation3300_4512_implies_Equation4272 G eq3300 eq4512
  have eq4275 := Equation3300_4512_implies_Equation4275 G eq3300 eq4512
  have eq4284 := Equation3300_4512_implies_Equation4284 G eq3300 eq4512
  have eq4304 := Equation3300_4512_implies_Equation4304 G eq3300 eq4512
  exact ⟨eq1, eq307, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq3300, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT102_implied_by_long (G : Type*) [Magma G] : AssociativeTheory102_long G -> AssociativeTheory102 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3300, _, _, _, _, h4512⟩ => ⟨h3300, h4512⟩

theorem AT102_equiv (G : Type*) [Magma G] : AssociativeTheory102 G <-> AssociativeTheory102_long G :=
Iff.intro (AT102_implies_long G) (AT102_implied_by_long G)

theorem AT103_implies_long (G : Type*) [Magma G] (h : AssociativeTheory103 G) : AssociativeTheory103_long G := by
  obtain ⟨eq309, eq3300, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3300_4512_implies_Equation307 G eq3300 eq4512
  have eq312 := Equation3300_4512_implies_Equation312 G eq3300 eq4512
  have eq315 := Equation3300_4512_implies_Equation315 G eq3300 eq4512
  have eq3253 := Equation3300_4512_implies_Equation3253 G eq3300 eq4512
  have eq3255 := Equation3300_4512_implies_Equation3255 G eq3300 eq4512
  have eq3258 := Equation3300_4512_implies_Equation3258 G eq3300 eq4512
  have eq3261 := Equation3300_4512_implies_Equation3261 G eq3300 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq3271 := Equation3300_4512_implies_Equation3271 G eq3300 eq4512
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq3278 := Equation3300_4512_implies_Equation3278 G eq3300 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq4272 := Equation3300_4512_implies_Equation4272 G eq3300 eq4512
  have eq4275 := Equation3300_4512_implies_Equation4275 G eq3300 eq4512
  have eq4284 := Equation3300_4512_implies_Equation4284 G eq3300 eq4512
  have eq4304 := Equation3300_4512_implies_Equation4304 G eq3300 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  exact ⟨eq1, eq307, eq309, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq3300, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4512⟩

theorem AT103_implied_by_long (G : Type*) [Magma G] : AssociativeTheory103_long G -> AssociativeTheory103 G :=
fun ⟨_, _, h309, _, _, _, _, _, _, _, _, _, _, _, h3300, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h3300, h4512⟩

theorem AT103_equiv (G : Type*) [Magma G] : AssociativeTheory103 G <-> AssociativeTheory103_long G :=
Iff.intro (AT103_implies_long G) (AT103_implied_by_long G)

theorem AT104_implies_long (G : Type*) [Magma G] (h : AssociativeTheory104 G) : AssociativeTheory104_long G := by
  obtain ⟨eq3306, eq4512⟩ := h
  have eq1 := Equation3306_4512_implies_Equation1 G eq3306 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact ⟨eq1, eq3253, eq3306, eq4512⟩

theorem AT104_implied_by_long (G : Type*) [Magma G] : AssociativeTheory104_long G -> AssociativeTheory104 G :=
fun ⟨_, _, h3306, h4512⟩ => ⟨h3306, h4512⟩

theorem AT104_equiv (G : Type*) [Magma G] : AssociativeTheory104 G <-> AssociativeTheory104_long G :=
Iff.intro (AT104_implies_long G) (AT104_implied_by_long G)

theorem AT105_implies_long (G : Type*) [Magma G] (h : AssociativeTheory105 G) : AssociativeTheory105_long G := by
  obtain ⟨eq40, eq3306, eq4512⟩ := h
  have eq3350 := Equation40_3306_4512_implies_Equation3350 G eq40 eq3306 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq43 := Equation3350_4512_implies_Equation43 G eq3350 eq4512
  have eq3308 := Equation3350_4512_implies_Equation3308 G eq3350 eq4512
  have eq3315 := Equation3350_4512_implies_Equation3315 G eq3350 eq4512
  have eq3319 := Equation3350_4512_implies_Equation3319 G eq3350 eq4512
  have eq3323 := Equation3350_4512_implies_Equation3323 G eq3350 eq4512
  have eq3331 := Equation3350_4512_implies_Equation3331 G eq3350 eq4512
  have eq3334 := Equation3350_4512_implies_Equation3334 G eq3350 eq4512
  have eq3342 := Equation3350_4512_implies_Equation3342 G eq3350 eq4512
  have eq3346 := Equation3350_4512_implies_Equation3346 G eq3350 eq4512
  have eq3353 := Equation3350_4512_implies_Equation3353 G eq3350 eq4512
  have eq3388 := Equation3350_4512_implies_Equation3388 G eq3350 eq4512
  have eq3414 := Equation3350_4512_implies_Equation3414 G eq3350 eq4512
  have eq4273 := Equation3350_4512_implies_Equation4273 G eq3350 eq4512
  have eq4283 := Equation3350_4512_implies_Equation4283 G eq3350 eq4512
  have eq4305 := Equation3350_4512_implies_Equation4305 G eq3350 eq4512
  have eq4320 := Equation3350_4512_implies_Equation4320 G eq3350 eq4512
  have eq4325 := Equation3350_4512_implies_Equation4325 G eq3350 eq4512
  have eq4358 := Equation3350_4512_implies_Equation4358 G eq3350 eq4512
  have eq4362 := Equation3350_4512_implies_Equation4362 G eq3350 eq4512
  have eq4364 := Equation3350_4512_implies_Equation4364 G eq3350 eq4512
  have eq4369 := Equation3350_4512_implies_Equation4369 G eq3350 eq4512
  exact ⟨eq1, eq40, eq43, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq3306, eq3308, eq3315, eq3319, eq3323, eq3331, eq3334, eq3342, eq3346, eq3350, eq3353, eq3388, eq3414, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT105_implied_by_long (G : Type*) [Magma G] : AssociativeTheory105_long G -> AssociativeTheory105 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, h3306, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3306, h4512⟩

theorem AT105_equiv (G : Type*) [Magma G] : AssociativeTheory105 G <-> AssociativeTheory105_long G :=
Iff.intro (AT105_implies_long G) (AT105_implied_by_long G)

theorem AT106_implies_long (G : Type*) [Magma G] (h : AssociativeTheory106 G) : AssociativeTheory106_long G := by
  obtain ⟨eq43, eq3306, eq4512⟩ := h
  have eq3342 := Equation43_3306_4512_implies_Equation3342 G eq43 eq3306 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq3308 := Equation3342_4512_implies_Equation3308 G eq3342 eq4512
  have eq3315 := Equation3342_4512_implies_Equation3315 G eq3342 eq4512
  have eq3319 := Equation3342_4512_implies_Equation3319 G eq3342 eq4512
  have eq3346 := Equation3342_4512_implies_Equation3346 G eq3342 eq4512
  have eq3353 := Equation3342_4512_implies_Equation3353 G eq3342 eq4512
  exact ⟨eq1, eq43, eq3253, eq3306, eq3308, eq3315, eq3319, eq3342, eq3346, eq3353, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT106_implied_by_long (G : Type*) [Magma G] : AssociativeTheory106_long G -> AssociativeTheory106 G :=
fun ⟨_, h43, _, h3306, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h3306, h4512⟩

theorem AT106_equiv (G : Type*) [Magma G] : AssociativeTheory106 G <-> AssociativeTheory106_long G :=
Iff.intro (AT106_implies_long G) (AT106_implied_by_long G)

theorem AT107_implies_long (G : Type*) [Magma G] (h : AssociativeTheory107 G) : AssociativeTheory107_long G := by
  obtain ⟨eq3256, eq3306, eq4512⟩ := h
  have eq3331 := Equation3256_3306_4512_implies_Equation3331 G eq3256 eq3306 eq4512
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq3259 := Equation3331_4512_implies_Equation3259 G eq3331 eq4512
  have eq3261 := Equation3331_4512_implies_Equation3261 G eq3331 eq4512
  have eq3308 := Equation3331_4512_implies_Equation3308 G eq3331 eq4512
  have eq3315 := Equation3331_4512_implies_Equation3315 G eq3331 eq4512
  have eq3319 := Equation3331_4512_implies_Equation3319 G eq3331 eq4512
  have eq3323 := Equation3331_4512_implies_Equation3323 G eq3331 eq4512
  have eq3334 := Equation3331_4512_implies_Equation3334 G eq3331 eq4512
  have eq4270 := Equation3331_4512_implies_Equation4270 G eq3331 eq4512
  have eq4283 := Equation3331_4512_implies_Equation4283 G eq3331 eq4512
  have eq4358 := Equation3331_4512_implies_Equation4358 G eq3331 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq3306, eq3308, eq3315, eq3319, eq3323, eq3331, eq3334, eq4270, eq4283, eq4358, eq4512⟩

theorem AT107_implied_by_long (G : Type*) [Magma G] : AssociativeTheory107_long G -> AssociativeTheory107 G :=
fun ⟨_, _, h3256, _, _, h3306, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3256, h3306, h4512⟩

theorem AT107_equiv (G : Type*) [Magma G] : AssociativeTheory107 G <-> AssociativeTheory107_long G :=
Iff.intro (AT107_implies_long G) (AT107_implied_by_long G)

theorem AT108_implies_long (G : Type*) [Magma G] (h : AssociativeTheory108 G) : AssociativeTheory108_long G := by
  obtain ⟨eq3261, eq3306, eq4512⟩ := h
  have eq3334 := Equation3261_3306_4512_implies_Equation3334 G eq3261 eq3306 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq3319 := Equation3334_4512_implies_Equation3319 G eq3334 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3306, eq3319, eq3334, eq4512⟩

theorem AT108_implied_by_long (G : Type*) [Magma G] : AssociativeTheory108_long G -> AssociativeTheory108 G :=
fun ⟨_, _, h3261, h3306, _, _, h4512⟩ => ⟨h3261, h3306, h4512⟩

theorem AT108_equiv (G : Type*) [Magma G] : AssociativeTheory108 G <-> AssociativeTheory108_long G :=
Iff.intro (AT108_implies_long G) (AT108_implied_by_long G)

theorem AT109_implies_long (G : Type*) [Magma G] (h : AssociativeTheory109 G) : AssociativeTheory109_long G := by
  obtain ⟨eq3271, eq3306, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq3261 := Equation3271_4512_implies_Equation3261 G eq3271 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  have eq3414 := Equation3278_3306_4512_implies_Equation3414 G eq3278 eq3306 eq4512
  have eq3334 := Equation3261_3306_4512_implies_Equation3334 G eq3261 eq3306 eq4512
  have eq3319 := Equation3334_4512_implies_Equation3319 G eq3334 eq4512
  have eq3353 := Equation3414_4512_implies_Equation3353 G eq3414 eq4512
  have eq3346 := Equation3261_3353_4512_implies_Equation3346 G eq3261 eq3353 eq4512
  have eq3388 := Equation3261_3346_4512_implies_Equation3388 G eq3261 eq3346 eq4512
  have eq4320 := Equation3346_4512_implies_Equation4320 G eq3346 eq4512
  have eq4362 := Equation3388_4512_implies_Equation4362 G eq3388 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq3306, eq3319, eq3334, eq3346, eq3353, eq3388, eq3414, eq4275, eq4320, eq4362, eq4512⟩

theorem AT109_implied_by_long (G : Type*) [Magma G] : AssociativeTheory109_long G -> AssociativeTheory109 G :=
fun ⟨_, _, _, h3271, _, h3306, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3271, h3306, h4512⟩

theorem AT109_equiv (G : Type*) [Magma G] : AssociativeTheory109 G <-> AssociativeTheory109_long G :=
Iff.intro (AT109_implies_long G) (AT109_implied_by_long G)

theorem AT110_implies_long (G : Type*) [Magma G] (h : AssociativeTheory110 G) : AssociativeTheory110_long G := by
  obtain ⟨eq3278, eq3306, eq4512⟩ := h
  have eq3414 := Equation3278_3306_4512_implies_Equation3414 G eq3278 eq3306 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3414_4512_implies_Equation3253 G eq3414 eq4512
  have eq3353 := Equation3414_4512_implies_Equation3353 G eq3414 eq4512
  exact ⟨eq1, eq3253, eq3278, eq3306, eq3353, eq3414, eq4512⟩

theorem AT110_implied_by_long (G : Type*) [Magma G] : AssociativeTheory110_long G -> AssociativeTheory110 G :=
fun ⟨_, _, h3278, h3306, _, _, h4512⟩ => ⟨h3278, h3306, h4512⟩

theorem AT110_equiv (G : Type*) [Magma G] : AssociativeTheory110 G <-> AssociativeTheory110_long G :=
Iff.intro (AT110_implies_long G) (AT110_implied_by_long G)

theorem AT111_implies_long (G : Type*) [Magma G] (h : AssociativeTheory111 G) : AssociativeTheory111_long G := by
  obtain ⟨eq3308, eq4512⟩ := h
  have eq1 := Equation3308_4512_implies_Equation1 G eq3308 eq4512
  have eq3253 := Equation3308_4512_implies_Equation3253 G eq3308 eq4512
  have eq3306 := Equation3308_4512_implies_Equation3306 G eq3308 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq3319 := Equation3308_4512_implies_Equation3319 G eq3308 eq4512
  have eq4283 := Equation3308_4512_implies_Equation4283 G eq3308 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4512⟩

theorem AT111_implied_by_long (G : Type*) [Magma G] : AssociativeTheory111_long G -> AssociativeTheory111 G :=
fun ⟨_, _, _, h3308, _, _, _, h4512⟩ => ⟨h3308, h4512⟩

theorem AT111_equiv (G : Type*) [Magma G] : AssociativeTheory111 G <-> AssociativeTheory111_long G :=
Iff.intro (AT111_implies_long G) (AT111_implied_by_long G)

theorem AT112_implies_long (G : Type*) [Magma G] (h : AssociativeTheory112 G) : AssociativeTheory112_long G := by
  obtain ⟨eq8, eq3308, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq4283 := Equation3308_4512_implies_Equation4283 G eq3308 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4512⟩

theorem AT112_implied_by_long (G : Type*) [Magma G] : AssociativeTheory112_long G -> AssociativeTheory112 G :=
fun ⟨_, h8, _, _, _, h3308, _, _, _, h4512⟩ => ⟨h8, h3308, h4512⟩

theorem AT112_equiv (G : Type*) [Magma G] : AssociativeTheory112 G <-> AssociativeTheory112_long G :=
Iff.intro (AT112_implies_long G) (AT112_implied_by_long G)

theorem AT113_implies_long (G : Type*) [Magma G] (h : AssociativeTheory113 G) : AssociativeTheory113_long G := by
  obtain ⟨eq3315, eq4512⟩ := h
  have eq1 := Equation3315_4512_implies_Equation1 G eq3315 eq4512
  have eq3253 := Equation3315_4512_implies_Equation3253 G eq3315 eq4512
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact ⟨eq1, eq3253, eq3315, eq3319, eq4512⟩

theorem AT113_implied_by_long (G : Type*) [Magma G] : AssociativeTheory113_long G -> AssociativeTheory113 G :=
fun ⟨_, _, h3315, _, h4512⟩ => ⟨h3315, h4512⟩

theorem AT113_equiv (G : Type*) [Magma G] : AssociativeTheory113 G <-> AssociativeTheory113_long G :=
Iff.intro (AT113_implies_long G) (AT113_implied_by_long G)

theorem AT114_implies_long (G : Type*) [Magma G] (h : AssociativeTheory114 G) : AssociativeTheory114_long G := by
  obtain ⟨eq8, eq3315, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3315, eq3319, eq4512⟩

theorem AT114_implied_by_long (G : Type*) [Magma G] : AssociativeTheory114_long G -> AssociativeTheory114 G :=
fun ⟨_, h8, _, _, _, h3315, _, h4512⟩ => ⟨h8, h3315, h4512⟩

theorem AT114_equiv (G : Type*) [Magma G] : AssociativeTheory114 G <-> AssociativeTheory114_long G :=
Iff.intro (AT114_implies_long G) (AT114_implied_by_long G)

theorem AT115_implies_long (G : Type*) [Magma G] (h : AssociativeTheory115 G) : AssociativeTheory115_long G := by
  obtain ⟨eq3256, eq3315, eq4512⟩ := h
  have eq3323 := Equation3256_3315_4512_implies_Equation3323 G eq3256 eq3315 eq4512
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3315, eq3319, eq3323, eq4512⟩

theorem AT115_implied_by_long (G : Type*) [Magma G] : AssociativeTheory115_long G -> AssociativeTheory115 G :=
fun ⟨_, _, h3256, h3315, _, _, h4512⟩ => ⟨h3256, h3315, h4512⟩

theorem AT115_equiv (G : Type*) [Magma G] : AssociativeTheory115 G <-> AssociativeTheory115_long G :=
Iff.intro (AT115_implies_long G) (AT115_implied_by_long G)

theorem AT116_implies_long (G : Type*) [Magma G] (h : AssociativeTheory116 G) : AssociativeTheory116_long G := by
  obtain ⟨eq3306, eq3315, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3315, eq3319, eq4512⟩

theorem AT116_implied_by_long (G : Type*) [Magma G] : AssociativeTheory116_long G -> AssociativeTheory116 G :=
fun ⟨_, _, h3306, h3315, _, h4512⟩ => ⟨h3306, h3315, h4512⟩

theorem AT116_equiv (G : Type*) [Magma G] : AssociativeTheory116 G <-> AssociativeTheory116_long G :=
Iff.intro (AT116_implies_long G) (AT116_implied_by_long G)

theorem AT117_implies_long (G : Type*) [Magma G] (h : AssociativeTheory117 G) : AssociativeTheory117_long G := by
  obtain ⟨eq3316, eq4512⟩ := h
  have eq1 := Equation3316_4512_implies_Equation1 G eq3316 eq4512
  have eq307 := Equation3316_4512_implies_Equation307 G eq3316 eq4512
  have eq3253 := Equation3316_4512_implies_Equation3253 G eq3316 eq4512
  exact ⟨eq1, eq307, eq3253, eq3316, eq4512⟩

theorem AT117_implied_by_long (G : Type*) [Magma G] : AssociativeTheory117_long G -> AssociativeTheory117 G :=
fun ⟨_, _, _, h3316, h4512⟩ => ⟨h3316, h4512⟩

theorem AT117_equiv (G : Type*) [Magma G] : AssociativeTheory117 G <-> AssociativeTheory117_long G :=
Iff.intro (AT117_implies_long G) (AT117_implied_by_long G)

theorem AT118_implies_long (G : Type*) [Magma G] (h : AssociativeTheory118 G) : AssociativeTheory118_long G := by
  obtain ⟨eq323, eq3316, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq3316, eq4512⟩

theorem AT118_implied_by_long (G : Type*) [Magma G] : AssociativeTheory118_long G -> AssociativeTheory118 G :=
fun ⟨_, _, h323, _, _, h3316, h4512⟩ => ⟨h323, h3316, h4512⟩

theorem AT118_equiv (G : Type*) [Magma G] : AssociativeTheory118 G <-> AssociativeTheory118_long G :=
Iff.intro (AT118_implies_long G) (AT118_implied_by_long G)

theorem AT119_implies_long (G : Type*) [Magma G] (h : AssociativeTheory119 G) : AssociativeTheory119_long G := by
  obtain ⟨eq326, eq3316, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3316_4512_implies_Equation307 G eq3316 eq4512
  have eq3253 := Equation3316_4512_implies_Equation3253 G eq3316 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3316, eq3319, eq4512⟩

theorem AT119_implied_by_long (G : Type*) [Magma G] : AssociativeTheory119_long G -> AssociativeTheory119 G :=
fun ⟨_, _, h326, _, h3316, _, h4512⟩ => ⟨h326, h3316, h4512⟩

theorem AT119_equiv (G : Type*) [Magma G] : AssociativeTheory119 G <-> AssociativeTheory119_long G :=
Iff.intro (AT119_implies_long G) (AT119_implied_by_long G)

theorem AT120_implies_long (G : Type*) [Magma G] (h : AssociativeTheory120 G) : AssociativeTheory120_long G := by
  obtain ⟨eq3319, eq4512⟩ := h
  have eq1 := Equation3319_4512_implies_Equation1 G eq3319 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact ⟨eq1, eq3253, eq3319, eq4512⟩

theorem AT120_implied_by_long (G : Type*) [Magma G] : AssociativeTheory120_long G -> AssociativeTheory120 G :=
fun ⟨_, _, h3319, h4512⟩ => ⟨h3319, h4512⟩

theorem AT120_equiv (G : Type*) [Magma G] : AssociativeTheory120 G <-> AssociativeTheory120_long G :=
Iff.intro (AT120_implies_long G) (AT120_implied_by_long G)

theorem AT121_implies_long (G : Type*) [Magma G] (h : AssociativeTheory121 G) : AssociativeTheory121_long G := by
  obtain ⟨eq3306, eq3319, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq4512⟩

theorem AT121_implied_by_long (G : Type*) [Magma G] : AssociativeTheory121_long G -> AssociativeTheory121 G :=
fun ⟨_, _, h3306, h3319, h4512⟩ => ⟨h3306, h3319, h4512⟩

theorem AT121_equiv (G : Type*) [Magma G] : AssociativeTheory121 G <-> AssociativeTheory121_long G :=
Iff.intro (AT121_implies_long G) (AT121_implied_by_long G)

theorem AT122_implies_long (G : Type*) [Magma G] (h : AssociativeTheory122 G) : AssociativeTheory122_long G := by
  obtain ⟨eq3346, eq4512⟩ := h
  have eq1 := Equation3346_4512_implies_Equation1 G eq3346 eq4512
  have eq3253 := Equation3346_4512_implies_Equation3253 G eq3346 eq4512
  have eq3306 := Equation3346_4512_implies_Equation3306 G eq3346 eq4512
  have eq3319 := Equation3346_4512_implies_Equation3319 G eq3346 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  have eq4320 := Equation3346_4512_implies_Equation4320 G eq3346 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4512⟩

theorem AT122_implied_by_long (G : Type*) [Magma G] : AssociativeTheory122_long G -> AssociativeTheory122 G :=
fun ⟨_, _, _, _, h3346, _, _, h4512⟩ => ⟨h3346, h4512⟩

theorem AT122_equiv (G : Type*) [Magma G] : AssociativeTheory122 G <-> AssociativeTheory122_long G :=
Iff.intro (AT122_implies_long G) (AT122_implied_by_long G)

theorem AT123_implies_long (G : Type*) [Magma G] (h : AssociativeTheory123 G) : AssociativeTheory123_long G := by
  obtain ⟨eq8, eq3346, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  have eq4320 := Equation3346_4512_implies_Equation4320 G eq3346 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4512⟩

theorem AT123_implied_by_long (G : Type*) [Magma G] : AssociativeTheory123_long G -> AssociativeTheory123 G :=
fun ⟨_, h8, _, _, _, _, h3346, _, _, h4512⟩ => ⟨h8, h3346, h4512⟩

theorem AT123_equiv (G : Type*) [Magma G] : AssociativeTheory123 G <-> AssociativeTheory123_long G :=
Iff.intro (AT123_implies_long G) (AT123_implied_by_long G)

theorem AT124_implies_long (G : Type*) [Magma G] (h : AssociativeTheory124 G) : AssociativeTheory124_long G := by
  obtain ⟨eq3353, eq4512⟩ := h
  have eq1 := Equation3353_4512_implies_Equation1 G eq3353 eq4512
  have eq3253 := Equation3353_4512_implies_Equation3253 G eq3353 eq4512
  have eq3306 := Equation3353_4512_implies_Equation3306 G eq3353 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3353, eq4512⟩

theorem AT124_implied_by_long (G : Type*) [Magma G] : AssociativeTheory124_long G -> AssociativeTheory124 G :=
fun ⟨_, _, _, h3353, h4512⟩ => ⟨h3353, h4512⟩

theorem AT124_equiv (G : Type*) [Magma G] : AssociativeTheory124 G <-> AssociativeTheory124_long G :=
Iff.intro (AT124_implies_long G) (AT124_implied_by_long G)

theorem AT125_implies_long (G : Type*) [Magma G] (h : AssociativeTheory125 G) : AssociativeTheory125_long G := by
  obtain ⟨eq8, eq3353, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq3353, eq4512⟩

theorem AT125_implied_by_long (G : Type*) [Magma G] : AssociativeTheory125_long G -> AssociativeTheory125 G :=
fun ⟨_, h8, _, _, _, _, h3353, h4512⟩ => ⟨h8, h3353, h4512⟩

theorem AT125_equiv (G : Type*) [Magma G] : AssociativeTheory125 G <-> AssociativeTheory125_long G :=
Iff.intro (AT125_implies_long G) (AT125_implied_by_long G)

theorem AT126_implies_long (G : Type*) [Magma G] (h : AssociativeTheory126 G) : AssociativeTheory126_long G := by
  obtain ⟨eq3319, eq3353, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3353_4512_implies_Equation3253 G eq3353 eq4512
  have eq3306 := Equation3353_4512_implies_Equation3306 G eq3353 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq3353, eq4512⟩

theorem AT126_implied_by_long (G : Type*) [Magma G] : AssociativeTheory126_long G -> AssociativeTheory126 G :=
fun ⟨_, _, _, h3319, h3353, h4512⟩ => ⟨h3319, h3353, h4512⟩

theorem AT126_equiv (G : Type*) [Magma G] : AssociativeTheory126 G <-> AssociativeTheory126_long G :=
Iff.intro (AT126_implies_long G) (AT126_implied_by_long G)

theorem AT127_implies_long (G : Type*) [Magma G] (h : AssociativeTheory127 G) : AssociativeTheory127_long G := by
  obtain ⟨eq4268, eq4512⟩ := h
  have eq1 := Equation4268_4512_implies_Equation1 G eq4268 eq4512
  exact ⟨eq1, eq4268, eq4512⟩

theorem AT127_implied_by_long (G : Type*) [Magma G] : AssociativeTheory127_long G -> AssociativeTheory127 G :=
fun ⟨_, h4268, h4512⟩ => ⟨h4268, h4512⟩

theorem AT127_equiv (G : Type*) [Magma G] : AssociativeTheory127 G <-> AssociativeTheory127_long G :=
Iff.intro (AT127_implies_long G) (AT127_implied_by_long G)

theorem AT128_implies_long (G : Type*) [Magma G] (h : AssociativeTheory128 G) : AssociativeTheory128_long G := by
  obtain ⟨eq43, eq4268, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq43, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT128_implied_by_long (G : Type*) [Magma G] : AssociativeTheory128_long G -> AssociativeTheory128 G :=
fun ⟨_, h43, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4268, h4512⟩

theorem AT128_equiv (G : Type*) [Magma G] : AssociativeTheory128 G <-> AssociativeTheory128_long G :=
Iff.intro (AT128_implies_long G) (AT128_implied_by_long G)

theorem AT129_implies_long (G : Type*) [Magma G] (h : AssociativeTheory129 G) : AssociativeTheory129_long G := by
  obtain ⟨eq4269, eq4512⟩ := h
  have eq1 := Equation4269_4512_implies_Equation1 G eq4269 eq4512
  exact ⟨eq1, eq4269, eq4512⟩

theorem AT129_implied_by_long (G : Type*) [Magma G] : AssociativeTheory129_long G -> AssociativeTheory129 G :=
fun ⟨_, h4269, h4512⟩ => ⟨h4269, h4512⟩

theorem AT129_equiv (G : Type*) [Magma G] : AssociativeTheory129 G <-> AssociativeTheory129_long G :=
Iff.intro (AT129_implies_long G) (AT129_implied_by_long G)

theorem AT130_implies_long (G : Type*) [Magma G] (h : AssociativeTheory130 G) : AssociativeTheory130_long G := by
  obtain ⟨eq4268, eq4269, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4283, eq4286, eq4512⟩

theorem AT130_implied_by_long (G : Type*) [Magma G] : AssociativeTheory130_long G -> AssociativeTheory130 G :=
fun ⟨_, h4268, h4269, _, _, h4512⟩ => ⟨h4268, h4269, h4512⟩

theorem AT130_equiv (G : Type*) [Magma G] : AssociativeTheory130 G <-> AssociativeTheory130_long G :=
Iff.intro (AT130_implies_long G) (AT130_implied_by_long G)

theorem AT131_implies_long (G : Type*) [Magma G] (h : AssociativeTheory131 G) : AssociativeTheory131_long G := by
  obtain ⟨eq4270, eq4512⟩ := h
  have eq1 := Equation4270_4512_implies_Equation1 G eq4270 eq4512
  exact ⟨eq1, eq4270, eq4512⟩

theorem AT131_implied_by_long (G : Type*) [Magma G] : AssociativeTheory131_long G -> AssociativeTheory131 G :=
fun ⟨_, h4270, h4512⟩ => ⟨h4270, h4512⟩

theorem AT131_equiv (G : Type*) [Magma G] : AssociativeTheory131 G <-> AssociativeTheory131_long G :=
Iff.intro (AT131_implies_long G) (AT131_implied_by_long G)

theorem AT132_implies_long (G : Type*) [Magma G] (h : AssociativeTheory132 G) : AssociativeTheory132_long G := by
  obtain ⟨eq43, eq4270, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq43, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT132_implied_by_long (G : Type*) [Magma G] : AssociativeTheory132_long G -> AssociativeTheory132 G :=
fun ⟨_, h43, h4270, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4270, h4512⟩

theorem AT132_equiv (G : Type*) [Magma G] : AssociativeTheory132 G <-> AssociativeTheory132_long G :=
Iff.intro (AT132_implies_long G) (AT132_implied_by_long G)

theorem AT133_implies_long (G : Type*) [Magma G] (h : AssociativeTheory133 G) : AssociativeTheory133_long G := by
  obtain ⟨eq4268, eq4270, eq4512⟩ := h
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  exact ⟨eq1, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem AT133_implied_by_long (G : Type*) [Magma G] : AssociativeTheory133_long G -> AssociativeTheory133 G :=
fun ⟨_, h4268, h4270, _, _, h4512⟩ => ⟨h4268, h4270, h4512⟩

theorem AT133_equiv (G : Type*) [Magma G] : AssociativeTheory133 G <-> AssociativeTheory133_long G :=
Iff.intro (AT133_implies_long G) (AT133_implied_by_long G)

theorem AT134_implies_long (G : Type*) [Magma G] (h : AssociativeTheory134 G) : AssociativeTheory134_long G := by
  obtain ⟨eq4269, eq4270, eq4512⟩ := h
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  exact ⟨eq1, eq4269, eq4270, eq4314, eq4318, eq4512⟩

theorem AT134_implied_by_long (G : Type*) [Magma G] : AssociativeTheory134_long G -> AssociativeTheory134 G :=
fun ⟨_, h4269, h4270, _, _, h4512⟩ => ⟨h4269, h4270, h4512⟩

theorem AT134_equiv (G : Type*) [Magma G] : AssociativeTheory134 G <-> AssociativeTheory134_long G :=
Iff.intro (AT134_implies_long G) (AT134_implied_by_long G)

theorem AT135_implies_long (G : Type*) [Magma G] (h : AssociativeTheory135 G) : AssociativeTheory135_long G := by
  obtain ⟨eq4268, eq4269, eq4270, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4512⟩

theorem AT135_implied_by_long (G : Type*) [Magma G] : AssociativeTheory135_long G -> AssociativeTheory135 G :=
fun ⟨_, h4268, h4269, h4270, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4269, h4270, h4512⟩

theorem AT135_equiv (G : Type*) [Magma G] : AssociativeTheory135 G <-> AssociativeTheory135_long G :=
Iff.intro (AT135_implies_long G) (AT135_implied_by_long G)

theorem AT136_implies_long (G : Type*) [Magma G] (h : AssociativeTheory136 G) : AssociativeTheory136_long G := by
  obtain ⟨eq4271, eq4512⟩ := h
  have eq1 := Equation4271_4512_implies_Equation1 G eq4271 eq4512
  have eq4268 := Equation4271_4512_implies_Equation4268 G eq4271 eq4512
  have eq4269 := Equation4271_4512_implies_Equation4269 G eq4271 eq4512
  have eq4270 := Equation4271_4512_implies_Equation4270 G eq4271 eq4512
  have eq4283 := Equation4271_4512_implies_Equation4283 G eq4271 eq4512
  have eq4284 := Equation4271_4512_implies_Equation4284 G eq4271 eq4512
  have eq4286 := Equation4271_4512_implies_Equation4286 G eq4271 eq4512
  have eq4287 := Equation4271_4512_implies_Equation4287 G eq4271 eq4512
  have eq4288 := Equation4271_4512_implies_Equation4288 G eq4271 eq4512
  have eq4314 := Equation4271_4512_implies_Equation4314 G eq4271 eq4512
  have eq4315 := Equation4271_4512_implies_Equation4315 G eq4271 eq4512
  have eq4318 := Equation4271_4512_implies_Equation4318 G eq4271 eq4512
  have eq4358 := Equation4271_4512_implies_Equation4358 G eq4271 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4271, eq4283, eq4284, eq4286, eq4287, eq4288, eq4314, eq4315, eq4318, eq4358, eq4512⟩

theorem AT136_implied_by_long (G : Type*) [Magma G] : AssociativeTheory136_long G -> AssociativeTheory136 G :=
fun ⟨_, _, _, _, h4271, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4271, h4512⟩

theorem AT136_equiv (G : Type*) [Magma G] : AssociativeTheory136 G <-> AssociativeTheory136_long G :=
Iff.intro (AT136_implies_long G) (AT136_implied_by_long G)

theorem AT137_implies_long (G : Type*) [Magma G] (h : AssociativeTheory137 G) : AssociativeTheory137_long G := by
  obtain ⟨eq43, eq4271, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4268 := Equation4271_4512_implies_Equation4268 G eq4271 eq4512
  have eq4269 := Equation4271_4512_implies_Equation4269 G eq4271 eq4512
  have eq4270 := Equation4271_4512_implies_Equation4270 G eq4271 eq4512
  have eq4284 := Equation4271_4512_implies_Equation4284 G eq4271 eq4512
  have eq4286 := Equation4271_4512_implies_Equation4286 G eq4271 eq4512
  have eq4287 := Equation4271_4512_implies_Equation4287 G eq4271 eq4512
  have eq4288 := Equation4271_4512_implies_Equation4288 G eq4271 eq4512
  have eq4314 := Equation4271_4512_implies_Equation4314 G eq4271 eq4512
  have eq4315 := Equation4271_4512_implies_Equation4315 G eq4271 eq4512
  have eq4318 := Equation4271_4512_implies_Equation4318 G eq4271 eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4274 := Equation4271_4272_4512_implies_Equation4274 G eq4271 eq4272 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4278 := Equation4272_4287_4512_implies_Equation4278 G eq4272 eq4287 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4276 := Equation4274_4512_implies_Equation4276 G eq4274 eq4512
  have eq4300 := Equation4274_4512_implies_Equation4300 G eq4274 eq4512
  exact ⟨eq1, eq43, eq4268, eq4269, eq4270, eq4271, eq4272, eq4273, eq4274, eq4275, eq4276, eq4277, eq4278, eq4279, eq4280, eq4283, eq4284, eq4286, eq4287, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4300, eq4301, eq4304, eq4305, eq4314, eq4315, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT137_implied_by_long (G : Type*) [Magma G] : AssociativeTheory137_long G -> AssociativeTheory137 G :=
fun ⟨_, h43, _, _, _, h4271, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4271, h4512⟩

theorem AT137_equiv (G : Type*) [Magma G] : AssociativeTheory137 G <-> AssociativeTheory137_long G :=
Iff.intro (AT137_implies_long G) (AT137_implied_by_long G)

theorem AT138_implies_long (G : Type*) [Magma G] (h : AssociativeTheory138 G) : AssociativeTheory138_long G := by
  obtain ⟨eq4272, eq4512⟩ := h
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  exact ⟨eq1, eq4272, eq4512⟩

theorem AT138_implied_by_long (G : Type*) [Magma G] : AssociativeTheory138_long G -> AssociativeTheory138 G :=
fun ⟨_, h4272, h4512⟩ => ⟨h4272, h4512⟩

theorem AT138_equiv (G : Type*) [Magma G] : AssociativeTheory138 G <-> AssociativeTheory138_long G :=
Iff.intro (AT138_implies_long G) (AT138_implied_by_long G)

theorem AT139_implies_long (G : Type*) [Magma G] (h : AssociativeTheory139 G) : AssociativeTheory139_long G := by
  obtain ⟨eq4268, eq4272, eq4512⟩ := h
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4270 := Equation4299_4512_implies_Equation4270 G eq4299 eq4512
  have eq4275 := Equation4299_4512_implies_Equation4275 G eq4299 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  have eq4290 := Equation4299_4512_implies_Equation4290 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4297 := Equation4299_4512_implies_Equation4297 G eq4299 eq4512
  have eq4304 := Equation4299_4512_implies_Equation4304 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  exact ⟨eq1, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4512⟩

theorem AT139_implied_by_long (G : Type*) [Magma G] : AssociativeTheory139_long G -> AssociativeTheory139 G :=
fun ⟨_, h4268, _, h4272, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4272, h4512⟩

theorem AT139_equiv (G : Type*) [Magma G] : AssociativeTheory139 G <-> AssociativeTheory139_long G :=
Iff.intro (AT139_implies_long G) (AT139_implied_by_long G)

theorem AT140_implies_long (G : Type*) [Magma G] (h : AssociativeTheory140 G) : AssociativeTheory140_long G := by
  obtain ⟨eq4269, eq4272, eq4512⟩ := h
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4320, eq4327, eq4512⟩

theorem AT140_implied_by_long (G : Type*) [Magma G] : AssociativeTheory140_long G -> AssociativeTheory140 G :=
fun ⟨_, h4269, h4272, _, _, h4512⟩ => ⟨h4269, h4272, h4512⟩

theorem AT140_equiv (G : Type*) [Magma G] : AssociativeTheory140 G <-> AssociativeTheory140_long G :=
Iff.intro (AT140_implies_long G) (AT140_implied_by_long G)

theorem AT141_implies_long (G : Type*) [Magma G] (h : AssociativeTheory141 G) : AssociativeTheory141_long G := by
  obtain ⟨eq4268, eq4269, eq4272, eq4512⟩ := h
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  have eq4270 := Equation4299_4512_implies_Equation4270 G eq4299 eq4512
  have eq4275 := Equation4299_4512_implies_Equation4275 G eq4299 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  have eq4290 := Equation4299_4512_implies_Equation4290 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4297 := Equation4299_4512_implies_Equation4297 G eq4299 eq4512
  have eq4304 := Equation4299_4512_implies_Equation4304 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  have eq4314 := Equation4320_4343_4512_implies_Equation4314 G eq4320 eq4343 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4512⟩

theorem AT141_implied_by_long (G : Type*) [Magma G] : AssociativeTheory141_long G -> AssociativeTheory141 G :=
fun ⟨_, h4268, h4269, _, h4272, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4269, h4272, h4512⟩

theorem AT141_equiv (G : Type*) [Magma G] : AssociativeTheory141 G <-> AssociativeTheory141_long G :=
Iff.intro (AT141_implies_long G) (AT141_implied_by_long G)

theorem AT142_implies_long (G : Type*) [Magma G] (h : AssociativeTheory142 G) : AssociativeTheory142_long G := by
  obtain ⟨eq4270, eq4272, eq4512⟩ := h
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4343, eq4512⟩

theorem AT142_implied_by_long (G : Type*) [Magma G] : AssociativeTheory142_long G -> AssociativeTheory142 G :=
fun ⟨_, h4270, h4272, _, _, _, h4512⟩ => ⟨h4270, h4272, h4512⟩

theorem AT142_equiv (G : Type*) [Magma G] : AssociativeTheory142 G <-> AssociativeTheory142_long G :=
Iff.intro (AT142_implies_long G) (AT142_implied_by_long G)

theorem AT143_implies_long (G : Type*) [Magma G] (h : AssociativeTheory143 G) : AssociativeTheory143_long G := by
  obtain ⟨eq4269, eq4270, eq4272, eq4512⟩ := h
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4273 := Equation4269_4276_4512_implies_Equation4273 G eq4269 eq4276 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4279 := Equation4331_4512_implies_Equation4279 G eq4331 eq4512
  have eq4325 := Equation4331_4512_implies_Equation4325 G eq4331 eq4512
  exact ⟨eq1, eq4269, eq4270, eq4272, eq4273, eq4276, eq4279, eq4280, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4512⟩

theorem AT143_implied_by_long (G : Type*) [Magma G] : AssociativeTheory143_long G -> AssociativeTheory143 G :=
fun ⟨_, h4269, h4270, h4272, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4269, h4270, h4272, h4512⟩

theorem AT143_equiv (G : Type*) [Magma G] : AssociativeTheory143 G <-> AssociativeTheory143_long G :=
Iff.intro (AT143_implies_long G) (AT143_implied_by_long G)

theorem AT144_implies_long (G : Type*) [Magma G] (h : AssociativeTheory144 G) : AssociativeTheory144_long G := by
  obtain ⟨eq4271, eq4272, eq4512⟩ := h
  have eq4274 := Equation4271_4272_4512_implies_Equation4274 G eq4271 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4268 := Equation4274_4512_implies_Equation4268 G eq4274 eq4512
  have eq4269 := Equation4274_4512_implies_Equation4269 G eq4274 eq4512
  have eq4270 := Equation4274_4512_implies_Equation4270 G eq4274 eq4512
  have eq4273 := Equation4274_4512_implies_Equation4273 G eq4274 eq4512
  have eq4275 := Equation4274_4512_implies_Equation4275 G eq4274 eq4512
  have eq4276 := Equation4274_4512_implies_Equation4276 G eq4274 eq4512
  have eq4277 := Equation4274_4512_implies_Equation4277 G eq4274 eq4512
  have eq4278 := Equation4274_4512_implies_Equation4278 G eq4274 eq4512
  have eq4279 := Equation4274_4512_implies_Equation4279 G eq4274 eq4512
  have eq4280 := Equation4274_4512_implies_Equation4280 G eq4274 eq4512
  have eq4283 := Equation4274_4512_implies_Equation4283 G eq4274 eq4512
  have eq4284 := Equation4274_4512_implies_Equation4284 G eq4274 eq4512
  have eq4286 := Equation4274_4512_implies_Equation4286 G eq4274 eq4512
  have eq4287 := Equation4274_4512_implies_Equation4287 G eq4274 eq4512
  have eq4288 := Equation4274_4512_implies_Equation4288 G eq4274 eq4512
  have eq4290 := Equation4274_4512_implies_Equation4290 G eq4274 eq4512
  have eq4291 := Equation4274_4512_implies_Equation4291 G eq4274 eq4512
  have eq4293 := Equation4274_4512_implies_Equation4293 G eq4274 eq4512
  have eq4296 := Equation4274_4512_implies_Equation4296 G eq4274 eq4512
  have eq4297 := Equation4274_4512_implies_Equation4297 G eq4274 eq4512
  have eq4299 := Equation4274_4512_implies_Equation4299 G eq4274 eq4512
  have eq4300 := Equation4274_4512_implies_Equation4300 G eq4274 eq4512
  have eq4301 := Equation4274_4512_implies_Equation4301 G eq4274 eq4512
  have eq4304 := Equation4274_4512_implies_Equation4304 G eq4274 eq4512
  have eq4305 := Equation4274_4512_implies_Equation4305 G eq4274 eq4512
  have eq4314 := Equation4274_4512_implies_Equation4314 G eq4274 eq4512
  have eq4315 := Equation4274_4512_implies_Equation4315 G eq4274 eq4512
  have eq4318 := Equation4274_4512_implies_Equation4318 G eq4274 eq4512
  have eq4320 := Equation4274_4512_implies_Equation4320 G eq4274 eq4512
  have eq4321 := Equation4274_4512_implies_Equation4321 G eq4274 eq4512
  have eq4325 := Equation4274_4512_implies_Equation4325 G eq4274 eq4512
  have eq4327 := Equation4274_4512_implies_Equation4327 G eq4274 eq4512
  have eq4331 := Equation4274_4512_implies_Equation4331 G eq4274 eq4512
  have eq4343 := Equation4274_4512_implies_Equation4343 G eq4274 eq4512
  have eq4358 := Equation4274_4512_implies_Equation4358 G eq4274 eq4512
  have eq4362 := Equation4274_4512_implies_Equation4362 G eq4274 eq4512
  have eq4364 := Equation4274_4512_implies_Equation4364 G eq4274 eq4512
  have eq4369 := Equation4274_4512_implies_Equation4369 G eq4274 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4271, eq4272, eq4273, eq4274, eq4275, eq4276, eq4277, eq4278, eq4279, eq4280, eq4283, eq4284, eq4286, eq4287, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4300, eq4301, eq4304, eq4305, eq4314, eq4315, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT144_implied_by_long (G : Type*) [Magma G] : AssociativeTheory144_long G -> AssociativeTheory144 G :=
fun ⟨_, _, _, _, h4271, h4272, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4271, h4272, h4512⟩

theorem AT144_equiv (G : Type*) [Magma G] : AssociativeTheory144 G <-> AssociativeTheory144_long G :=
Iff.intro (AT144_implies_long G) (AT144_implied_by_long G)

theorem AT145_implies_long (G : Type*) [Magma G] (h : AssociativeTheory145 G) : AssociativeTheory145_long G := by
  obtain ⟨eq4273, eq4512⟩ := h
  have eq1 := Equation4273_4512_implies_Equation1 G eq4273 eq4512
  exact ⟨eq1, eq4273, eq4512⟩

theorem AT145_implied_by_long (G : Type*) [Magma G] : AssociativeTheory145_long G -> AssociativeTheory145 G :=
fun ⟨_, h4273, h4512⟩ => ⟨h4273, h4512⟩

theorem AT145_equiv (G : Type*) [Magma G] : AssociativeTheory145 G <-> AssociativeTheory145_long G :=
Iff.intro (AT145_implies_long G) (AT145_implied_by_long G)

theorem AT146_implies_long (G : Type*) [Magma G] (h : AssociativeTheory146 G) : AssociativeTheory146_long G := by
  obtain ⟨eq40, eq4273, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4512⟩

theorem AT146_implied_by_long (G : Type*) [Magma G] : AssociativeTheory146_long G -> AssociativeTheory146 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, h4273, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h4273, h4512⟩

theorem AT146_equiv (G : Type*) [Magma G] : AssociativeTheory146 G <-> AssociativeTheory146_long G :=
Iff.intro (AT146_implies_long G) (AT146_implied_by_long G)

theorem AT147_implies_long (G : Type*) [Magma G] (h : AssociativeTheory147 G) : AssociativeTheory147_long G := by
  obtain ⟨eq4268, eq4273, eq4512⟩ := h
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4269 := Equation4301_4512_implies_Equation4269 G eq4301 eq4512
  have eq4275 := Equation4301_4512_implies_Equation4275 G eq4301 eq4512
  have eq4276 := Equation4301_4512_implies_Equation4276 G eq4301 eq4512
  have eq4277 := Equation4301_4512_implies_Equation4277 G eq4301 eq4512
  have eq4279 := Equation4301_4512_implies_Equation4279 G eq4301 eq4512
  have eq4283 := Equation4301_4512_implies_Equation4283 G eq4301 eq4512
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  have eq4291 := Equation4301_4512_implies_Equation4291 G eq4301 eq4512
  have eq4293 := Equation4301_4512_implies_Equation4293 G eq4301 eq4512
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  have eq4305 := Equation4301_4512_implies_Equation4305 G eq4301 eq4512
  have eq4321 := Equation4301_4512_implies_Equation4321 G eq4301 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4273, eq4275, eq4276, eq4277, eq4279, eq4283, eq4286, eq4291, eq4293, eq4296, eq4301, eq4305, eq4321, eq4512⟩

theorem AT147_implied_by_long (G : Type*) [Magma G] : AssociativeTheory147_long G -> AssociativeTheory147 G :=
fun ⟨_, h4268, _, h4273, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4273, h4512⟩

theorem AT147_equiv (G : Type*) [Magma G] : AssociativeTheory147 G <-> AssociativeTheory147_long G :=
Iff.intro (AT147_implies_long G) (AT147_implied_by_long G)

theorem AT148_implies_long (G : Type*) [Magma G] (h : AssociativeTheory148 G) : AssociativeTheory148_long G := by
  obtain ⟨eq4269, eq4273, eq4512⟩ := h
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4321, eq4512⟩

theorem AT148_implied_by_long (G : Type*) [Magma G] : AssociativeTheory148_long G -> AssociativeTheory148 G :=
fun ⟨_, h4269, h4273, _, _, _, h4512⟩ => ⟨h4269, h4273, h4512⟩

theorem AT148_equiv (G : Type*) [Magma G] : AssociativeTheory148 G <-> AssociativeTheory148_long G :=
Iff.intro (AT148_implies_long G) (AT148_implied_by_long G)

theorem AT149_implies_long (G : Type*) [Magma G] (h : AssociativeTheory149 G) : AssociativeTheory149_long G := by
  obtain ⟨eq4270, eq4273, eq4512⟩ := h
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4320, eq4325, eq4512⟩

theorem AT149_implied_by_long (G : Type*) [Magma G] : AssociativeTheory149_long G -> AssociativeTheory149 G :=
fun ⟨_, h4270, h4273, _, _, h4512⟩ => ⟨h4270, h4273, h4512⟩

theorem AT149_equiv (G : Type*) [Magma G] : AssociativeTheory149 G <-> AssociativeTheory149_long G :=
Iff.intro (AT149_implies_long G) (AT149_implied_by_long G)

theorem AT150_implies_long (G : Type*) [Magma G] (h : AssociativeTheory150 G) : AssociativeTheory150_long G := by
  obtain ⟨eq4275, eq4512⟩ := h
  have eq1 := Equation4275_4512_implies_Equation1 G eq4275 eq4512
  exact ⟨eq1, eq4275, eq4512⟩

theorem AT150_implied_by_long (G : Type*) [Magma G] : AssociativeTheory150_long G -> AssociativeTheory150 G :=
fun ⟨_, h4275, h4512⟩ => ⟨h4275, h4512⟩

theorem AT150_equiv (G : Type*) [Magma G] : AssociativeTheory150 G <-> AssociativeTheory150_long G :=
Iff.intro (AT150_implies_long G) (AT150_implied_by_long G)

theorem AT151_implies_long (G : Type*) [Magma G] (h : AssociativeTheory151 G) : AssociativeTheory151_long G := by
  obtain ⟨eq4268, eq4275, eq4512⟩ := h
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4512⟩

theorem AT151_implied_by_long (G : Type*) [Magma G] : AssociativeTheory151_long G -> AssociativeTheory151 G :=
fun ⟨_, h4268, h4275, _, _, _, h4512⟩ => ⟨h4268, h4275, h4512⟩

theorem AT151_equiv (G : Type*) [Magma G] : AssociativeTheory151 G <-> AssociativeTheory151_long G :=
Iff.intro (AT151_implies_long G) (AT151_implied_by_long G)

theorem AT152_implies_long (G : Type*) [Magma G] (h : AssociativeTheory152 G) : AssociativeTheory152_long G := by
  obtain ⟨eq4269, eq4275, eq4512⟩ := h
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  exact ⟨eq1, eq4269, eq4275, eq4291, eq4296, eq4512⟩

theorem AT152_implied_by_long (G : Type*) [Magma G] : AssociativeTheory152_long G -> AssociativeTheory152 G :=
fun ⟨_, h4269, h4275, _, _, h4512⟩ => ⟨h4269, h4275, h4512⟩

theorem AT152_equiv (G : Type*) [Magma G] : AssociativeTheory152 G <-> AssociativeTheory152_long G :=
Iff.intro (AT152_implies_long G) (AT152_implied_by_long G)

theorem AT153_implies_long (G : Type*) [Magma G] (h : AssociativeTheory153 G) : AssociativeTheory153_long G := by
  obtain ⟨eq4270, eq4275, eq4512⟩ := h
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4297_4512_implies_Equation4290 G eq4297 eq4512
  exact ⟨eq1, eq4270, eq4275, eq4290, eq4297, eq4512⟩

theorem AT153_implied_by_long (G : Type*) [Magma G] : AssociativeTheory153_long G -> AssociativeTheory153 G :=
fun ⟨_, h4270, h4275, _, _, h4512⟩ => ⟨h4270, h4275, h4512⟩

theorem AT153_equiv (G : Type*) [Magma G] : AssociativeTheory153 G <-> AssociativeTheory153_long G :=
Iff.intro (AT153_implies_long G) (AT153_implied_by_long G)

theorem AT154_implies_long (G : Type*) [Magma G] (h : AssociativeTheory154 G) : AssociativeTheory154_long G := by
  obtain ⟨eq4272, eq4275, eq4512⟩ := h
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4284 := Equation4304_4512_implies_Equation4284 G eq4304 eq4512
  exact ⟨eq1, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem AT154_implied_by_long (G : Type*) [Magma G] : AssociativeTheory154_long G -> AssociativeTheory154 G :=
fun ⟨_, h4272, h4275, _, _, h4512⟩ => ⟨h4272, h4275, h4512⟩

theorem AT154_equiv (G : Type*) [Magma G] : AssociativeTheory154 G <-> AssociativeTheory154_long G :=
Iff.intro (AT154_implies_long G) (AT154_implied_by_long G)

theorem AT155_implies_long (G : Type*) [Magma G] (h : AssociativeTheory155 G) : AssociativeTheory155_long G := by
  obtain ⟨eq4269, eq4272, eq4275, eq4512⟩ := h
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4284 := Equation4304_4512_implies_Equation4284 G eq4304 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4512⟩

theorem AT155_implied_by_long (G : Type*) [Magma G] : AssociativeTheory155_long G -> AssociativeTheory155 G :=
fun ⟨_, h4269, h4272, h4275, _, _, _, _, _, _, h4512⟩ => ⟨h4269, h4272, h4275, h4512⟩

theorem AT155_equiv (G : Type*) [Magma G] : AssociativeTheory155 G <-> AssociativeTheory155_long G :=
Iff.intro (AT155_implies_long G) (AT155_implied_by_long G)

theorem AT156_implies_long (G : Type*) [Magma G] (h : AssociativeTheory156 G) : AssociativeTheory156_long G := by
  obtain ⟨eq4273, eq4275, eq4512⟩ := h
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  exact ⟨eq1, eq4273, eq4275, eq4283, eq4305, eq4512⟩

theorem AT156_implied_by_long (G : Type*) [Magma G] : AssociativeTheory156_long G -> AssociativeTheory156 G :=
fun ⟨_, h4273, h4275, _, _, h4512⟩ => ⟨h4273, h4275, h4512⟩

theorem AT156_equiv (G : Type*) [Magma G] : AssociativeTheory156 G <-> AssociativeTheory156_long G :=
Iff.intro (AT156_implies_long G) (AT156_implied_by_long G)

theorem AT157_implies_long (G : Type*) [Magma G] (h : AssociativeTheory157 G) : AssociativeTheory157_long G := by
  obtain ⟨eq4270, eq4273, eq4275, eq4512⟩ := h
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  have eq4290 := Equation4297_4512_implies_Equation4290 G eq4297 eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4512⟩

theorem AT157_implied_by_long (G : Type*) [Magma G] : AssociativeTheory157_long G -> AssociativeTheory157 G :=
fun ⟨_, h4270, h4273, h4275, _, _, _, _, _, _, h4512⟩ => ⟨h4270, h4273, h4275, h4512⟩

theorem AT157_equiv (G : Type*) [Magma G] : AssociativeTheory157 G <-> AssociativeTheory157_long G :=
Iff.intro (AT157_implies_long G) (AT157_implied_by_long G)

theorem AT158_implies_long (G : Type*) [Magma G] (h : AssociativeTheory158 G) : AssociativeTheory158_long G := by
  obtain ⟨eq4276, eq4512⟩ := h
  have eq1 := Equation4276_4512_implies_Equation1 G eq4276 eq4512
  exact ⟨eq1, eq4276, eq4512⟩

theorem AT158_implied_by_long (G : Type*) [Magma G] : AssociativeTheory158_long G -> AssociativeTheory158 G :=
fun ⟨_, h4276, h4512⟩ => ⟨h4276, h4512⟩

theorem AT158_equiv (G : Type*) [Magma G] : AssociativeTheory158 G <-> AssociativeTheory158_long G :=
Iff.intro (AT158_implies_long G) (AT158_implied_by_long G)

theorem AT159_implies_long (G : Type*) [Magma G] (h : AssociativeTheory159 G) : AssociativeTheory159_long G := by
  obtain ⟨eq43, eq4276, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  exact ⟨eq1, eq43, eq4276, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT159_implied_by_long (G : Type*) [Magma G] : AssociativeTheory159_long G -> AssociativeTheory159 G :=
fun ⟨_, h43, h4276, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4276, h4512⟩

theorem AT159_equiv (G : Type*) [Magma G] : AssociativeTheory159 G <-> AssociativeTheory159_long G :=
Iff.intro (AT159_implies_long G) (AT159_implied_by_long G)

theorem AT160_implies_long (G : Type*) [Magma G] (h : AssociativeTheory160 G) : AssociativeTheory160_long G := by
  obtain ⟨eq4278, eq4512⟩ := h
  have eq1 := Equation4278_4512_implies_Equation1 G eq4278 eq4512
  have eq4269 := Equation4278_4512_implies_Equation4269 G eq4278 eq4512
  have eq4272 := Equation4278_4512_implies_Equation4272 G eq4278 eq4512
  have eq4275 := Equation4278_4512_implies_Equation4275 G eq4278 eq4512
  have eq4284 := Equation4278_4512_implies_Equation4284 G eq4278 eq4512
  have eq4287 := Equation4278_4512_implies_Equation4287 G eq4278 eq4512
  have eq4291 := Equation4278_4512_implies_Equation4291 G eq4278 eq4512
  have eq4296 := Equation4278_4512_implies_Equation4296 G eq4278 eq4512
  have eq4300 := Equation4278_4512_implies_Equation4300 G eq4278 eq4512
  have eq4304 := Equation4278_4512_implies_Equation4304 G eq4278 eq4512
  have eq4320 := Equation4278_4512_implies_Equation4320 G eq4278 eq4512
  have eq4327 := Equation4278_4512_implies_Equation4327 G eq4278 eq4512
  have eq4362 := Equation4278_4512_implies_Equation4362 G eq4278 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4275, eq4278, eq4284, eq4287, eq4291, eq4296, eq4300, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT160_implied_by_long (G : Type*) [Magma G] : AssociativeTheory160_long G -> AssociativeTheory160 G :=
fun ⟨_, _, _, _, h4278, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4278, h4512⟩

theorem AT160_equiv (G : Type*) [Magma G] : AssociativeTheory160 G <-> AssociativeTheory160_long G :=
Iff.intro (AT160_implies_long G) (AT160_implied_by_long G)

theorem AT161_implies_long (G : Type*) [Magma G] (h : AssociativeTheory161 G) : AssociativeTheory161_long G := by
  obtain ⟨eq4283, eq4512⟩ := h
  have eq1 := Equation4283_4512_implies_Equation1 G eq4283 eq4512
  exact ⟨eq1, eq4283, eq4512⟩

theorem AT161_implied_by_long (G : Type*) [Magma G] : AssociativeTheory161_long G -> AssociativeTheory161 G :=
fun ⟨_, h4283, h4512⟩ => ⟨h4283, h4512⟩

theorem AT161_equiv (G : Type*) [Magma G] : AssociativeTheory161 G <-> AssociativeTheory161_long G :=
Iff.intro (AT161_implies_long G) (AT161_implied_by_long G)

theorem AT162_implies_long (G : Type*) [Magma G] (h : AssociativeTheory162 G) : AssociativeTheory162_long G := by
  obtain ⟨eq47, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq47, eq4283, eq4512⟩

theorem AT162_implied_by_long (G : Type*) [Magma G] : AssociativeTheory162_long G -> AssociativeTheory162 G :=
fun ⟨_, h47, h4283, h4512⟩ => ⟨h47, h4283, h4512⟩

theorem AT162_equiv (G : Type*) [Magma G] : AssociativeTheory162 G <-> AssociativeTheory162_long G :=
Iff.intro (AT162_implies_long G) (AT162_implied_by_long G)

theorem AT163_implies_long (G : Type*) [Magma G] (h : AssociativeTheory163 G) : AssociativeTheory163_long G := by
  obtain ⟨eq56, eq4283, eq4512⟩ := h
  have eq4358 := Equation56_4283_4512_implies_Equation4358 G eq56 eq4283 eq4512
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact ⟨eq1, eq47, eq56, eq4283, eq4358, eq4512⟩

theorem AT163_implied_by_long (G : Type*) [Magma G] : AssociativeTheory163_long G -> AssociativeTheory163 G :=
fun ⟨_, _, h56, h4283, _, h4512⟩ => ⟨h56, h4283, h4512⟩

theorem AT163_equiv (G : Type*) [Magma G] : AssociativeTheory163 G <-> AssociativeTheory163_long G :=
Iff.intro (AT163_implies_long G) (AT163_implied_by_long G)

theorem AT164_implies_long (G : Type*) [Magma G] (h : AssociativeTheory164 G) : AssociativeTheory164_long G := by
  obtain ⟨eq307, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4512⟩

theorem AT164_implied_by_long (G : Type*) [Magma G] : AssociativeTheory164_long G -> AssociativeTheory164 G :=
fun ⟨_, h307, _, h4283, h4512⟩ => ⟨h307, h4283, h4512⟩

theorem AT164_equiv (G : Type*) [Magma G] : AssociativeTheory164 G <-> AssociativeTheory164_long G :=
Iff.intro (AT164_implies_long G) (AT164_implied_by_long G)

theorem AT165_implies_long (G : Type*) [Magma G] (h : AssociativeTheory165 G) : AssociativeTheory165_long G := by
  obtain ⟨eq326, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4283, eq4512⟩

theorem AT165_implied_by_long (G : Type*) [Magma G] : AssociativeTheory165_long G -> AssociativeTheory165 G :=
fun ⟨_, _, h326, _, _, h4283, h4512⟩ => ⟨h326, h4283, h4512⟩

theorem AT165_equiv (G : Type*) [Magma G] : AssociativeTheory165 G <-> AssociativeTheory165_long G :=
Iff.intro (AT165_implies_long G) (AT165_implied_by_long G)

theorem AT166_implies_long (G : Type*) [Magma G] (h : AssociativeTheory166 G) : AssociativeTheory166_long G := by
  obtain ⟨eq411, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq411, eq4283, eq4512⟩

theorem AT166_implied_by_long (G : Type*) [Magma G] : AssociativeTheory166_long G -> AssociativeTheory166 G :=
fun ⟨_, h411, h4283, h4512⟩ => ⟨h411, h4283, h4512⟩

theorem AT166_equiv (G : Type*) [Magma G] : AssociativeTheory166 G <-> AssociativeTheory166_long G :=
Iff.intro (AT166_implies_long G) (AT166_implied_by_long G)

theorem AT167_implies_long (G : Type*) [Magma G] (h : AssociativeTheory167 G) : AssociativeTheory167_long G := by
  obtain ⟨eq440, eq4283, eq4512⟩ := h
  have eq4358 := Equation440_4283_4512_implies_Equation4358 G eq440 eq4283 eq4512
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact ⟨eq1, eq411, eq440, eq4283, eq4358, eq4512⟩

theorem AT167_implied_by_long (G : Type*) [Magma G] : AssociativeTheory167_long G -> AssociativeTheory167 G :=
fun ⟨_, _, h440, h4283, _, h4512⟩ => ⟨h440, h4283, h4512⟩

theorem AT167_equiv (G : Type*) [Magma G] : AssociativeTheory167 G <-> AssociativeTheory167_long G :=
Iff.intro (AT167_implies_long G) (AT167_implied_by_long G)

theorem AT168_implies_long (G : Type*) [Magma G] (h : AssociativeTheory168 G) : AssociativeTheory168_long G := by
  obtain ⟨eq3253, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq3253, eq4283, eq4512⟩

theorem AT168_implied_by_long (G : Type*) [Magma G] : AssociativeTheory168_long G -> AssociativeTheory168 G :=
fun ⟨_, h3253, h4283, h4512⟩ => ⟨h3253, h4283, h4512⟩

theorem AT168_equiv (G : Type*) [Magma G] : AssociativeTheory168 G <-> AssociativeTheory168_long G :=
Iff.intro (AT168_implies_long G) (AT168_implied_by_long G)

theorem AT169_implies_long (G : Type*) [Magma G] (h : AssociativeTheory169 G) : AssociativeTheory169_long G := by
  obtain ⟨eq3256, eq4283, eq4512⟩ := h
  have eq3259 := Equation3256_4283_4512_implies_Equation3259 G eq3256 eq4283 eq4512
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq4270, eq4283, eq4512⟩

theorem AT169_implied_by_long (G : Type*) [Magma G] : AssociativeTheory169_long G -> AssociativeTheory169 G :=
fun ⟨_, _, h3256, _, _, _, h4283, h4512⟩ => ⟨h3256, h4283, h4512⟩

theorem AT169_equiv (G : Type*) [Magma G] : AssociativeTheory169 G <-> AssociativeTheory169_long G :=
Iff.intro (AT169_implies_long G) (AT169_implied_by_long G)

theorem AT170_implies_long (G : Type*) [Magma G] (h : AssociativeTheory170 G) : AssociativeTheory170_long G := by
  obtain ⟨eq3319, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact ⟨eq1, eq3253, eq3319, eq4283, eq4512⟩

theorem AT170_implied_by_long (G : Type*) [Magma G] : AssociativeTheory170_long G -> AssociativeTheory170 G :=
fun ⟨_, _, h3319, h4283, h4512⟩ => ⟨h3319, h4283, h4512⟩

theorem AT170_equiv (G : Type*) [Magma G] : AssociativeTheory170 G <-> AssociativeTheory170_long G :=
Iff.intro (AT170_implies_long G) (AT170_implied_by_long G)

theorem AT171_implies_long (G : Type*) [Magma G] (h : AssociativeTheory171 G) : AssociativeTheory171_long G := by
  obtain ⟨eq4270, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4270, eq4283, eq4512⟩

theorem AT171_implied_by_long (G : Type*) [Magma G] : AssociativeTheory171_long G -> AssociativeTheory171 G :=
fun ⟨_, h4270, h4283, h4512⟩ => ⟨h4270, h4283, h4512⟩

theorem AT171_equiv (G : Type*) [Magma G] : AssociativeTheory171 G <-> AssociativeTheory171_long G :=
Iff.intro (AT171_implies_long G) (AT171_implied_by_long G)

theorem AT172_implies_long (G : Type*) [Magma G] (h : AssociativeTheory172 G) : AssociativeTheory172_long G := by
  obtain ⟨eq4272, eq4283, eq4512⟩ := h
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4343, eq4512⟩

theorem AT172_implied_by_long (G : Type*) [Magma G] : AssociativeTheory172_long G -> AssociativeTheory172 G :=
fun ⟨_, _, h4272, _, _, h4283, _, h4512⟩ => ⟨h4272, h4283, h4512⟩

theorem AT172_equiv (G : Type*) [Magma G] : AssociativeTheory172 G <-> AssociativeTheory172_long G :=
Iff.intro (AT172_implies_long G) (AT172_implied_by_long G)

theorem AT173_implies_long (G : Type*) [Magma G] (h : AssociativeTheory173 G) : AssociativeTheory173_long G := by
  obtain ⟨eq4276, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4512⟩

theorem AT173_implied_by_long (G : Type*) [Magma G] : AssociativeTheory173_long G -> AssociativeTheory173 G :=
fun ⟨_, h4276, h4283, h4512⟩ => ⟨h4276, h4283, h4512⟩

theorem AT173_equiv (G : Type*) [Magma G] : AssociativeTheory173 G <-> AssociativeTheory173_long G :=
Iff.intro (AT173_implies_long G) (AT173_implied_by_long G)

theorem AT174_implies_long (G : Type*) [Magma G] (h : AssociativeTheory174 G) : AssociativeTheory174_long G := by
  obtain ⟨eq4284, eq4512⟩ := h
  have eq1 := Equation4284_4512_implies_Equation1 G eq4284 eq4512
  exact ⟨eq1, eq4284, eq4512⟩

theorem AT174_implied_by_long (G : Type*) [Magma G] : AssociativeTheory174_long G -> AssociativeTheory174 G :=
fun ⟨_, h4284, h4512⟩ => ⟨h4284, h4512⟩

theorem AT174_equiv (G : Type*) [Magma G] : AssociativeTheory174 G <-> AssociativeTheory174_long G :=
Iff.intro (AT174_implies_long G) (AT174_implied_by_long G)

theorem AT175_implies_long (G : Type*) [Magma G] (h : AssociativeTheory175 G) : AssociativeTheory175_long G := by
  obtain ⟨eq43, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq43, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT175_implied_by_long (G : Type*) [Magma G] : AssociativeTheory175_long G -> AssociativeTheory175 G :=
fun ⟨_, h43, _, h4284, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4284, h4512⟩

theorem AT175_equiv (G : Type*) [Magma G] : AssociativeTheory175 G <-> AssociativeTheory175_long G :=
Iff.intro (AT175_implies_long G) (AT175_implied_by_long G)

theorem AT176_implies_long (G : Type*) [Magma G] (h : AssociativeTheory176 G) : AssociativeTheory176_long G := by
  obtain ⟨eq307, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4512⟩

theorem AT176_implied_by_long (G : Type*) [Magma G] : AssociativeTheory176_long G -> AssociativeTheory176 G :=
fun ⟨_, h307, _, h4284, h4512⟩ => ⟨h307, h4284, h4512⟩

theorem AT176_equiv (G : Type*) [Magma G] : AssociativeTheory176 G <-> AssociativeTheory176_long G :=
Iff.intro (AT176_implies_long G) (AT176_implied_by_long G)

theorem AT177_implies_long (G : Type*) [Magma G] (h : AssociativeTheory177 G) : AssociativeTheory177_long G := by
  obtain ⟨eq43, eq307, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq43, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT177_implied_by_long (G : Type*) [Magma G] : AssociativeTheory177_long G -> AssociativeTheory177 G :=
fun ⟨_, h43, h307, _, _, h4284, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h307, h4284, h4512⟩

theorem AT177_equiv (G : Type*) [Magma G] : AssociativeTheory177 G <-> AssociativeTheory177_long G :=
Iff.intro (AT177_implies_long G) (AT177_implied_by_long G)

theorem AT178_implies_long (G : Type*) [Magma G] (h : AssociativeTheory178 G) : AssociativeTheory178_long G := by
  obtain ⟨eq4269, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4269, eq4284, eq4512⟩

theorem AT178_implied_by_long (G : Type*) [Magma G] : AssociativeTheory178_long G -> AssociativeTheory178 G :=
fun ⟨_, h4269, h4284, h4512⟩ => ⟨h4269, h4284, h4512⟩

theorem AT178_equiv (G : Type*) [Magma G] : AssociativeTheory178 G <-> AssociativeTheory178_long G :=
Iff.intro (AT178_implies_long G) (AT178_implied_by_long G)

theorem AT179_implies_long (G : Type*) [Magma G] (h : AssociativeTheory179 G) : AssociativeTheory179_long G := by
  obtain ⟨eq4273, eq4284, eq4512⟩ := h
  have eq4269 := Equation4273_4284_4512_implies_Equation4269 G eq4273 eq4284 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4284, eq4321, eq4512⟩

theorem AT179_implied_by_long (G : Type*) [Magma G] : AssociativeTheory179_long G -> AssociativeTheory179 G :=
fun ⟨_, _, h4273, _, _, h4284, _, h4512⟩ => ⟨h4273, h4284, h4512⟩

theorem AT179_equiv (G : Type*) [Magma G] : AssociativeTheory179 G <-> AssociativeTheory179_long G :=
Iff.intro (AT179_implies_long G) (AT179_implied_by_long G)

theorem AT180_implies_long (G : Type*) [Magma G] (h : AssociativeTheory180 G) : AssociativeTheory180_long G := by
  obtain ⟨eq4276, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4512⟩

theorem AT180_implied_by_long (G : Type*) [Magma G] : AssociativeTheory180_long G -> AssociativeTheory180 G :=
fun ⟨_, h4276, h4284, h4512⟩ => ⟨h4276, h4284, h4512⟩

theorem AT180_equiv (G : Type*) [Magma G] : AssociativeTheory180 G <-> AssociativeTheory180_long G :=
Iff.intro (AT180_implies_long G) (AT180_implied_by_long G)

theorem AT181_implies_long (G : Type*) [Magma G] (h : AssociativeTheory181 G) : AssociativeTheory181_long G := by
  obtain ⟨eq43, eq4276, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation43_4512_implies_Equation4283 G eq43 eq4512
  have eq4290 := Equation43_4512_implies_Equation4290 G eq43 eq4512
  have eq4320 := Equation43_4512_implies_Equation4320 G eq43 eq4512
  have eq4358 := Equation43_4512_implies_Equation4358 G eq43 eq4512
  have eq4362 := Equation43_4512_implies_Equation4362 G eq43 eq4512
  have eq4364 := Equation43_4512_implies_Equation4364 G eq43 eq4512
  have eq4369 := Equation43_4512_implies_Equation4369 G eq43 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq43, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT181_implied_by_long (G : Type*) [Magma G] : AssociativeTheory181_long G -> AssociativeTheory181 G :=
fun ⟨_, h43, h4276, _, h4284, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4276, h4284, h4512⟩

theorem AT181_equiv (G : Type*) [Magma G] : AssociativeTheory181 G <-> AssociativeTheory181_long G :=
Iff.intro (AT181_implies_long G) (AT181_implied_by_long G)

theorem AT182_implies_long (G : Type*) [Magma G] (h : AssociativeTheory182 G) : AssociativeTheory182_long G := by
  obtain ⟨eq4283, eq4284, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4284, eq4314, eq4512⟩

theorem AT182_implied_by_long (G : Type*) [Magma G] : AssociativeTheory182_long G -> AssociativeTheory182 G :=
fun ⟨_, h4283, h4284, _, h4512⟩ => ⟨h4283, h4284, h4512⟩

theorem AT182_equiv (G : Type*) [Magma G] : AssociativeTheory182 G <-> AssociativeTheory182_long G :=
Iff.intro (AT182_implies_long G) (AT182_implied_by_long G)

theorem AT183_implies_long (G : Type*) [Magma G] (h : AssociativeTheory183 G) : AssociativeTheory183_long G := by
  obtain ⟨eq307, eq4283, eq4284, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4314, eq4512⟩

theorem AT183_implied_by_long (G : Type*) [Magma G] : AssociativeTheory183_long G -> AssociativeTheory183 G :=
fun ⟨_, h307, _, h4283, h4284, _, h4512⟩ => ⟨h307, h4283, h4284, h4512⟩

theorem AT183_equiv (G : Type*) [Magma G] : AssociativeTheory183 G <-> AssociativeTheory183_long G :=
Iff.intro (AT183_implies_long G) (AT183_implied_by_long G)

theorem AT184_implies_long (G : Type*) [Magma G] (h : AssociativeTheory184 G) : AssociativeTheory184_long G := by
  obtain ⟨eq4276, eq4283, eq4284, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4314, eq4512⟩

theorem AT184_implied_by_long (G : Type*) [Magma G] : AssociativeTheory184_long G -> AssociativeTheory184 G :=
fun ⟨_, h4276, h4283, h4284, _, h4512⟩ => ⟨h4276, h4283, h4284, h4512⟩

theorem AT184_equiv (G : Type*) [Magma G] : AssociativeTheory184 G <-> AssociativeTheory184_long G :=
Iff.intro (AT184_implies_long G) (AT184_implied_by_long G)

theorem AT185_implies_long (G : Type*) [Magma G] (h : AssociativeTheory185 G) : AssociativeTheory185_long G := by
  obtain ⟨eq4287, eq4512⟩ := h
  have eq1 := Equation4287_4512_implies_Equation1 G eq4287 eq4512
  have eq4269 := Equation4287_4512_implies_Equation4269 G eq4287 eq4512
  have eq4284 := Equation4287_4512_implies_Equation4284 G eq4287 eq4512
  exact ⟨eq1, eq4269, eq4284, eq4287, eq4512⟩

theorem AT185_implied_by_long (G : Type*) [Magma G] : AssociativeTheory185_long G -> AssociativeTheory185 G :=
fun ⟨_, _, _, h4287, h4512⟩ => ⟨h4287, h4512⟩

theorem AT185_equiv (G : Type*) [Magma G] : AssociativeTheory185 G <-> AssociativeTheory185_long G :=
Iff.intro (AT185_implies_long G) (AT185_implied_by_long G)

theorem AT186_implies_long (G : Type*) [Magma G] (h : AssociativeTheory186 G) : AssociativeTheory186_long G := by
  obtain ⟨eq307, eq4287, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4269 := Equation4287_4512_implies_Equation4269 G eq4287 eq4512
  have eq4284 := Equation4287_4512_implies_Equation4284 G eq4287 eq4512
  have eq309 := Equation307_4269_4512_implies_Equation309 G eq307 eq4269 eq4512
  have eq3255 := Equation309_4512_implies_Equation3255 G eq309 eq4512
  have eq3258 := Equation309_4512_implies_Equation3258 G eq309 eq4512
  have eq3261 := Equation309_4512_implies_Equation3261 G eq309 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  exact ⟨eq1, eq307, eq309, eq3253, eq3255, eq3258, eq3261, eq3264, eq4269, eq4284, eq4287, eq4512⟩

theorem AT186_implied_by_long (G : Type*) [Magma G] : AssociativeTheory186_long G -> AssociativeTheory186 G :=
fun ⟨_, h307, _, _, _, _, _, _, _, _, h4287, h4512⟩ => ⟨h307, h4287, h4512⟩

theorem AT186_equiv (G : Type*) [Magma G] : AssociativeTheory186 G <-> AssociativeTheory186_long G :=
Iff.intro (AT186_implies_long G) (AT186_implied_by_long G)

theorem AT187_implies_long (G : Type*) [Magma G] (h : AssociativeTheory187 G) : AssociativeTheory187_long G := by
  obtain ⟨eq4290, eq4512⟩ := h
  have eq1 := Equation4290_4512_implies_Equation1 G eq4290 eq4512
  exact ⟨eq1, eq4290, eq4512⟩

theorem AT187_implied_by_long (G : Type*) [Magma G] : AssociativeTheory187_long G -> AssociativeTheory187 G :=
fun ⟨_, h4290, h4512⟩ => ⟨h4290, h4512⟩

theorem AT187_equiv (G : Type*) [Magma G] : AssociativeTheory187 G <-> AssociativeTheory187_long G :=
Iff.intro (AT187_implies_long G) (AT187_implied_by_long G)

theorem AT188_implies_long (G : Type*) [Magma G] (h : AssociativeTheory188 G) : AssociativeTheory188_long G := by
  obtain ⟨eq307, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4290, eq4512⟩

theorem AT188_implied_by_long (G : Type*) [Magma G] : AssociativeTheory188_long G -> AssociativeTheory188 G :=
fun ⟨_, h307, _, h4290, h4512⟩ => ⟨h307, h4290, h4512⟩

theorem AT188_equiv (G : Type*) [Magma G] : AssociativeTheory188 G <-> AssociativeTheory188_long G :=
Iff.intro (AT188_implies_long G) (AT188_implied_by_long G)

theorem AT189_implies_long (G : Type*) [Magma G] (h : AssociativeTheory189 G) : AssociativeTheory189_long G := by
  obtain ⟨eq411, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq411, eq4290, eq4512⟩

theorem AT189_implied_by_long (G : Type*) [Magma G] : AssociativeTheory189_long G -> AssociativeTheory189 G :=
fun ⟨_, h411, h4290, h4512⟩ => ⟨h411, h4290, h4512⟩

theorem AT189_equiv (G : Type*) [Magma G] : AssociativeTheory189 G <-> AssociativeTheory189_long G :=
Iff.intro (AT189_implies_long G) (AT189_implied_by_long G)

theorem AT190_implies_long (G : Type*) [Magma G] (h : AssociativeTheory190 G) : AssociativeTheory190_long G := by
  obtain ⟨eq3253, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq3253, eq4290, eq4512⟩

theorem AT190_implied_by_long (G : Type*) [Magma G] : AssociativeTheory190_long G -> AssociativeTheory190 G :=
fun ⟨_, h3253, h4290, h4512⟩ => ⟨h3253, h4290, h4512⟩

theorem AT190_equiv (G : Type*) [Magma G] : AssociativeTheory190 G <-> AssociativeTheory190_long G :=
Iff.intro (AT190_implies_long G) (AT190_implied_by_long G)

theorem AT191_implies_long (G : Type*) [Magma G] (h : AssociativeTheory191 G) : AssociativeTheory191_long G := by
  obtain ⟨eq4269, eq4290, eq4512⟩ := h
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4290, eq4321, eq4512⟩

theorem AT191_implied_by_long (G : Type*) [Magma G] : AssociativeTheory191_long G -> AssociativeTheory191 G :=
fun ⟨_, h4269, _, _, _, h4290, _, h4512⟩ => ⟨h4269, h4290, h4512⟩

theorem AT191_equiv (G : Type*) [Magma G] : AssociativeTheory191 G <-> AssociativeTheory191_long G :=
Iff.intro (AT191_implies_long G) (AT191_implied_by_long G)

theorem AT192_implies_long (G : Type*) [Magma G] (h : AssociativeTheory192 G) : AssociativeTheory192_long G := by
  obtain ⟨eq4273, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4273, eq4290, eq4512⟩

theorem AT192_implied_by_long (G : Type*) [Magma G] : AssociativeTheory192_long G -> AssociativeTheory192 G :=
fun ⟨_, h4273, h4290, h4512⟩ => ⟨h4273, h4290, h4512⟩

theorem AT192_equiv (G : Type*) [Magma G] : AssociativeTheory192 G <-> AssociativeTheory192_long G :=
Iff.intro (AT192_implies_long G) (AT192_implied_by_long G)

theorem AT193_implies_long (G : Type*) [Magma G] (h : AssociativeTheory193 G) : AssociativeTheory193_long G := by
  obtain ⟨eq4276, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4290, eq4512⟩

theorem AT193_implied_by_long (G : Type*) [Magma G] : AssociativeTheory193_long G -> AssociativeTheory193 G :=
fun ⟨_, h4276, h4290, h4512⟩ => ⟨h4276, h4290, h4512⟩

theorem AT193_equiv (G : Type*) [Magma G] : AssociativeTheory193 G <-> AssociativeTheory193_long G :=
Iff.intro (AT193_implies_long G) (AT193_implied_by_long G)

theorem AT194_implies_long (G : Type*) [Magma G] (h : AssociativeTheory194 G) : AssociativeTheory194_long G := by
  obtain ⟨eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4512⟩

theorem AT194_implied_by_long (G : Type*) [Magma G] : AssociativeTheory194_long G -> AssociativeTheory194 G :=
fun ⟨_, h4283, h4290, _, h4512⟩ => ⟨h4283, h4290, h4512⟩

theorem AT194_equiv (G : Type*) [Magma G] : AssociativeTheory194 G <-> AssociativeTheory194_long G :=
Iff.intro (AT194_implies_long G) (AT194_implied_by_long G)

theorem AT195_implies_long (G : Type*) [Magma G] (h : AssociativeTheory195 G) : AssociativeTheory195_long G := by
  obtain ⟨eq307, eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4512⟩

theorem AT195_implied_by_long (G : Type*) [Magma G] : AssociativeTheory195_long G -> AssociativeTheory195 G :=
fun ⟨_, h307, _, h4283, h4290, _, h4512⟩ => ⟨h307, h4283, h4290, h4512⟩

theorem AT195_equiv (G : Type*) [Magma G] : AssociativeTheory195 G <-> AssociativeTheory195_long G :=
Iff.intro (AT195_implies_long G) (AT195_implied_by_long G)

theorem AT196_implies_long (G : Type*) [Magma G] (h : AssociativeTheory196 G) : AssociativeTheory196_long G := by
  obtain ⟨eq3253, eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4512⟩

theorem AT196_implied_by_long (G : Type*) [Magma G] : AssociativeTheory196_long G -> AssociativeTheory196 G :=
fun ⟨_, h3253, h4283, h4290, _, h4512⟩ => ⟨h3253, h4283, h4290, h4512⟩

theorem AT196_equiv (G : Type*) [Magma G] : AssociativeTheory196 G <-> AssociativeTheory196_long G :=
Iff.intro (AT196_implies_long G) (AT196_implied_by_long G)

theorem AT197_implies_long (G : Type*) [Magma G] (h : AssociativeTheory197 G) : AssociativeTheory197_long G := by
  obtain ⟨eq4276, eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4512⟩

theorem AT197_implied_by_long (G : Type*) [Magma G] : AssociativeTheory197_long G -> AssociativeTheory197 G :=
fun ⟨_, h4276, h4283, h4290, _, h4512⟩ => ⟨h4276, h4283, h4290, h4512⟩

theorem AT197_equiv (G : Type*) [Magma G] : AssociativeTheory197 G <-> AssociativeTheory197_long G :=
Iff.intro (AT197_implies_long G) (AT197_implied_by_long G)

theorem AT198_implies_long (G : Type*) [Magma G] (h : AssociativeTheory198 G) : AssociativeTheory198_long G := by
  obtain ⟨eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4343, eq4512⟩

theorem AT198_implied_by_long (G : Type*) [Magma G] : AssociativeTheory198_long G -> AssociativeTheory198 G :=
fun ⟨_, h4284, h4290, _, _, h4512⟩ => ⟨h4284, h4290, h4512⟩

theorem AT198_equiv (G : Type*) [Magma G] : AssociativeTheory198 G <-> AssociativeTheory198_long G :=
Iff.intro (AT198_implies_long G) (AT198_implied_by_long G)

theorem AT199_implies_long (G : Type*) [Magma G] (h : AssociativeTheory199 G) : AssociativeTheory199_long G := by
  obtain ⟨eq307, eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4343, eq4512⟩

theorem AT199_implied_by_long (G : Type*) [Magma G] : AssociativeTheory199_long G -> AssociativeTheory199 G :=
fun ⟨_, h307, _, h4284, h4290, _, _, h4512⟩ => ⟨h307, h4284, h4290, h4512⟩

theorem AT199_equiv (G : Type*) [Magma G] : AssociativeTheory199 G <-> AssociativeTheory199_long G :=
Iff.intro (AT199_implies_long G) (AT199_implied_by_long G)

theorem AT200_implies_long (G : Type*) [Magma G] (h : AssociativeTheory200 G) : AssociativeTheory200_long G := by
  obtain ⟨eq4269, eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem AT200_implied_by_long (G : Type*) [Magma G] : AssociativeTheory200_long G -> AssociativeTheory200 G :=
fun ⟨_, h4269, _, _, _, h4284, h4290, _, _, _, h4512⟩ => ⟨h4269, h4284, h4290, h4512⟩

theorem AT200_equiv (G : Type*) [Magma G] : AssociativeTheory200 G <-> AssociativeTheory200_long G :=
Iff.intro (AT200_implies_long G) (AT200_implied_by_long G)

theorem AT201_implies_long (G : Type*) [Magma G] (h : AssociativeTheory201 G) : AssociativeTheory201_long G := by
  obtain ⟨eq4276, eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4343, eq4512⟩

theorem AT201_implied_by_long (G : Type*) [Magma G] : AssociativeTheory201_long G -> AssociativeTheory201 G :=
fun ⟨_, h4276, h4284, h4290, _, _, h4512⟩ => ⟨h4276, h4284, h4290, h4512⟩

theorem AT201_equiv (G : Type*) [Magma G] : AssociativeTheory201 G <-> AssociativeTheory201_long G :=
Iff.intro (AT201_implies_long G) (AT201_implied_by_long G)

theorem AT202_implies_long (G : Type*) [Magma G] (h : AssociativeTheory202 G) : AssociativeTheory202_long G := by
  obtain ⟨eq4283, eq4284, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT202_implied_by_long (G : Type*) [Magma G] : AssociativeTheory202_long G -> AssociativeTheory202 G :=
fun ⟨_, h4283, h4284, h4290, _, _, _, _, _, _, h4512⟩ => ⟨h4283, h4284, h4290, h4512⟩

theorem AT202_equiv (G : Type*) [Magma G] : AssociativeTheory202 G <-> AssociativeTheory202_long G :=
Iff.intro (AT202_implies_long G) (AT202_implied_by_long G)

theorem AT203_implies_long (G : Type*) [Magma G] (h : AssociativeTheory203 G) : AssociativeTheory203_long G := by
  obtain ⟨eq307, eq4283, eq4284, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT203_implied_by_long (G : Type*) [Magma G] : AssociativeTheory203_long G -> AssociativeTheory203 G :=
fun ⟨_, h307, _, h4283, h4284, h4290, _, _, _, _, _, _, h4512⟩ => ⟨h307, h4283, h4284, h4290, h4512⟩

theorem AT203_equiv (G : Type*) [Magma G] : AssociativeTheory203 G <-> AssociativeTheory203_long G :=
Iff.intro (AT203_implies_long G) (AT203_implied_by_long G)

theorem AT204_implies_long (G : Type*) [Magma G] (h : AssociativeTheory204 G) : AssociativeTheory204_long G := by
  obtain ⟨eq4276, eq4283, eq4284, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT204_implied_by_long (G : Type*) [Magma G] : AssociativeTheory204_long G -> AssociativeTheory204 G :=
fun ⟨_, h4276, h4283, h4284, h4290, _, _, _, _, _, _, h4512⟩ => ⟨h4276, h4283, h4284, h4290, h4512⟩

theorem AT204_equiv (G : Type*) [Magma G] : AssociativeTheory204 G <-> AssociativeTheory204_long G :=
Iff.intro (AT204_implies_long G) (AT204_implied_by_long G)

theorem AT205_implies_long (G : Type*) [Magma G] (h : AssociativeTheory205 G) : AssociativeTheory205_long G := by
  obtain ⟨eq4291, eq4512⟩ := h
  have eq1 := Equation4291_4512_implies_Equation1 G eq4291 eq4512
  exact ⟨eq1, eq4291, eq4512⟩

theorem AT205_implied_by_long (G : Type*) [Magma G] : AssociativeTheory205_long G -> AssociativeTheory205 G :=
fun ⟨_, h4291, h4512⟩ => ⟨h4291, h4512⟩

theorem AT205_equiv (G : Type*) [Magma G] : AssociativeTheory205 G <-> AssociativeTheory205_long G :=
Iff.intro (AT205_implies_long G) (AT205_implied_by_long G)

theorem AT206_implies_long (G : Type*) [Magma G] (h : AssociativeTheory206 G) : AssociativeTheory206_long G := by
  obtain ⟨eq307, eq4291, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4291, eq4512⟩

theorem AT206_implied_by_long (G : Type*) [Magma G] : AssociativeTheory206_long G -> AssociativeTheory206 G :=
fun ⟨_, h307, _, h4291, h4512⟩ => ⟨h307, h4291, h4512⟩

theorem AT206_equiv (G : Type*) [Magma G] : AssociativeTheory206 G <-> AssociativeTheory206_long G :=
Iff.intro (AT206_implies_long G) (AT206_implied_by_long G)

theorem AT207_implies_long (G : Type*) [Magma G] (h : AssociativeTheory207 G) : AssociativeTheory207_long G := by
  obtain ⟨eq312, eq4291, eq4512⟩ := h
  have eq1 := Equation312_4512_implies_Equation1 G eq312 eq4512
  have eq307 := Equation312_4512_implies_Equation307 G eq312 eq4512
  have eq3253 := Equation312_4512_implies_Equation3253 G eq312 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  exact ⟨eq1, eq307, eq312, eq3253, eq3258, eq3278, eq4272, eq4291, eq4512⟩

theorem AT207_implied_by_long (G : Type*) [Magma G] : AssociativeTheory207_long G -> AssociativeTheory207 G :=
fun ⟨_, _, h312, _, _, _, _, h4291, h4512⟩ => ⟨h312, h4291, h4512⟩

theorem AT207_equiv (G : Type*) [Magma G] : AssociativeTheory207 G <-> AssociativeTheory207_long G :=
Iff.intro (AT207_implies_long G) (AT207_implied_by_long G)

theorem AT208_implies_long (G : Type*) [Magma G] (h : AssociativeTheory208 G) : AssociativeTheory208_long G := by
  obtain ⟨eq326, eq4291, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4291, eq4512⟩

theorem AT208_implied_by_long (G : Type*) [Magma G] : AssociativeTheory208_long G -> AssociativeTheory208 G :=
fun ⟨_, _, h326, _, _, h4291, h4512⟩ => ⟨h326, h4291, h4512⟩

theorem AT208_equiv (G : Type*) [Magma G] : AssociativeTheory208 G <-> AssociativeTheory208_long G :=
Iff.intro (AT208_implies_long G) (AT208_implied_by_long G)

theorem AT209_implies_long (G : Type*) [Magma G] (h : AssociativeTheory209 G) : AssociativeTheory209_long G := by
  obtain ⟨eq4270, eq4291, eq4512⟩ := h
  have eq4272 := Equation4270_4291_4512_implies_Equation4272 G eq4270 eq4291 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4291, eq4343, eq4512⟩

theorem AT209_implied_by_long (G : Type*) [Magma G] : AssociativeTheory209_long G -> AssociativeTheory209 G :=
fun ⟨_, h4270, _, _, _, h4291, _, h4512⟩ => ⟨h4270, h4291, h4512⟩

theorem AT209_equiv (G : Type*) [Magma G] : AssociativeTheory209 G <-> AssociativeTheory209_long G :=
Iff.intro (AT209_implies_long G) (AT209_implied_by_long G)

theorem AT210_implies_long (G : Type*) [Magma G] (h : AssociativeTheory210 G) : AssociativeTheory210_long G := by
  obtain ⟨eq4272, eq4291, eq4512⟩ := h
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  exact ⟨eq1, eq4272, eq4291, eq4512⟩

theorem AT210_implied_by_long (G : Type*) [Magma G] : AssociativeTheory210_long G -> AssociativeTheory210 G :=
fun ⟨_, h4272, h4291, h4512⟩ => ⟨h4272, h4291, h4512⟩

theorem AT210_equiv (G : Type*) [Magma G] : AssociativeTheory210 G <-> AssociativeTheory210_long G :=
Iff.intro (AT210_implies_long G) (AT210_implied_by_long G)

theorem AT211_implies_long (G : Type*) [Magma G] (h : AssociativeTheory211 G) : AssociativeTheory211_long G := by
  obtain ⟨eq4276, eq4291, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4291, eq4512⟩

theorem AT211_implied_by_long (G : Type*) [Magma G] : AssociativeTheory211_long G -> AssociativeTheory211 G :=
fun ⟨_, h4276, h4291, h4512⟩ => ⟨h4276, h4291, h4512⟩

theorem AT211_equiv (G : Type*) [Magma G] : AssociativeTheory211 G <-> AssociativeTheory211_long G :=
Iff.intro (AT211_implies_long G) (AT211_implied_by_long G)

theorem AT212_implies_long (G : Type*) [Magma G] (h : AssociativeTheory212 G) : AssociativeTheory212_long G := by
  obtain ⟨eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4512⟩

theorem AT212_implied_by_long (G : Type*) [Magma G] : AssociativeTheory212_long G -> AssociativeTheory212 G :=
fun ⟨_, h4283, h4291, _, _, h4512⟩ => ⟨h4283, h4291, h4512⟩

theorem AT212_equiv (G : Type*) [Magma G] : AssociativeTheory212 G <-> AssociativeTheory212_long G :=
Iff.intro (AT212_implies_long G) (AT212_implied_by_long G)

theorem AT213_implies_long (G : Type*) [Magma G] (h : AssociativeTheory213 G) : AssociativeTheory213_long G := by
  obtain ⟨eq307, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4291, eq4293, eq4321, eq4512⟩

theorem AT213_implied_by_long (G : Type*) [Magma G] : AssociativeTheory213_long G -> AssociativeTheory213 G :=
fun ⟨_, h307, _, h4283, h4291, _, _, h4512⟩ => ⟨h307, h4283, h4291, h4512⟩

theorem AT213_equiv (G : Type*) [Magma G] : AssociativeTheory213 G <-> AssociativeTheory213_long G :=
Iff.intro (AT213_implies_long G) (AT213_implied_by_long G)

theorem AT214_implies_long (G : Type*) [Magma G] (h : AssociativeTheory214 G) : AssociativeTheory214_long G := by
  obtain ⟨eq326, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4291_4512_implies_Equation1 G eq4291 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  have eq4358 := Equation326_4293_4512_implies_Equation4358 G eq326 eq4293 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem AT214_implied_by_long (G : Type*) [Magma G] : AssociativeTheory214_long G -> AssociativeTheory214 G :=
fun ⟨_, _, h326, _, _, h4283, h4291, _, _, _, h4512⟩ => ⟨h326, h4283, h4291, h4512⟩

theorem AT214_equiv (G : Type*) [Magma G] : AssociativeTheory214 G <-> AssociativeTheory214_long G :=
Iff.intro (AT214_implies_long G) (AT214_implied_by_long G)

theorem AT215_implies_long (G : Type*) [Magma G] (h : AssociativeTheory215 G) : AssociativeTheory215_long G := by
  obtain ⟨eq4270, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq4272 := Equation4270_4291_4512_implies_Equation4272 G eq4270 eq4291 eq4512
  have eq1 := Equation4291_4512_implies_Equation1 G eq4291 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4291, eq4293, eq4321, eq4343, eq4512⟩

theorem AT215_implied_by_long (G : Type*) [Magma G] : AssociativeTheory215_long G -> AssociativeTheory215 G :=
fun ⟨_, h4270, _, _, _, h4283, h4291, _, _, _, h4512⟩ => ⟨h4270, h4283, h4291, h4512⟩

theorem AT215_equiv (G : Type*) [Magma G] : AssociativeTheory215 G <-> AssociativeTheory215_long G :=
Iff.intro (AT215_implies_long G) (AT215_implied_by_long G)

theorem AT216_implies_long (G : Type*) [Magma G] (h : AssociativeTheory216 G) : AssociativeTheory216_long G := by
  obtain ⟨eq4276, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4512⟩

theorem AT216_implied_by_long (G : Type*) [Magma G] : AssociativeTheory216_long G -> AssociativeTheory216 G :=
fun ⟨_, h4276, h4283, h4291, _, _, h4512⟩ => ⟨h4276, h4283, h4291, h4512⟩

theorem AT216_equiv (G : Type*) [Magma G] : AssociativeTheory216 G <-> AssociativeTheory216_long G :=
Iff.intro (AT216_implies_long G) (AT216_implied_by_long G)

theorem AT217_implies_long (G : Type*) [Magma G] (h : AssociativeTheory217 G) : AssociativeTheory217_long G := by
  obtain ⟨eq4284, eq4291, eq4512⟩ := h
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4291, eq4320, eq4512⟩

theorem AT217_implied_by_long (G : Type*) [Magma G] : AssociativeTheory217_long G -> AssociativeTheory217 G :=
fun ⟨_, h4284, h4291, _, h4512⟩ => ⟨h4284, h4291, h4512⟩

theorem AT217_equiv (G : Type*) [Magma G] : AssociativeTheory217 G <-> AssociativeTheory217_long G :=
Iff.intro (AT217_implies_long G) (AT217_implied_by_long G)

theorem AT218_implies_long (G : Type*) [Magma G] (h : AssociativeTheory218 G) : AssociativeTheory218_long G := by
  obtain ⟨eq307, eq4284, eq4291, eq4512⟩ := h
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4291, eq4320, eq4512⟩

theorem AT218_implied_by_long (G : Type*) [Magma G] : AssociativeTheory218_long G -> AssociativeTheory218 G :=
fun ⟨_, h307, _, h4284, h4291, _, h4512⟩ => ⟨h307, h4284, h4291, h4512⟩

theorem AT218_equiv (G : Type*) [Magma G] : AssociativeTheory218 G <-> AssociativeTheory218_long G :=
Iff.intro (AT218_implies_long G) (AT218_implied_by_long G)

theorem AT219_implies_long (G : Type*) [Magma G] (h : AssociativeTheory219 G) : AssociativeTheory219_long G := by
  obtain ⟨eq4276, eq4284, eq4291, eq4512⟩ := h
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4291, eq4320, eq4512⟩

theorem AT219_implied_by_long (G : Type*) [Magma G] : AssociativeTheory219_long G -> AssociativeTheory219 G :=
fun ⟨_, h4276, h4284, h4291, _, h4512⟩ => ⟨h4276, h4284, h4291, h4512⟩

theorem AT219_equiv (G : Type*) [Magma G] : AssociativeTheory219 G <-> AssociativeTheory219_long G :=
Iff.intro (AT219_implies_long G) (AT219_implied_by_long G)

theorem AT220_implies_long (G : Type*) [Magma G] (h : AssociativeTheory220 G) : AssociativeTheory220_long G := by
  obtain ⟨eq4290, eq4291, eq4512⟩ := h
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4290, eq4291, eq4314, eq4512⟩

theorem AT220_implied_by_long (G : Type*) [Magma G] : AssociativeTheory220_long G -> AssociativeTheory220 G :=
fun ⟨_, h4290, h4291, _, h4512⟩ => ⟨h4290, h4291, h4512⟩

theorem AT220_equiv (G : Type*) [Magma G] : AssociativeTheory220 G <-> AssociativeTheory220_long G :=
Iff.intro (AT220_implies_long G) (AT220_implied_by_long G)

theorem AT221_implies_long (G : Type*) [Magma G] (h : AssociativeTheory221 G) : AssociativeTheory221_long G := by
  obtain ⟨eq4276, eq4290, eq4291, eq4512⟩ := h
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4290, eq4291, eq4314, eq4512⟩

theorem AT221_implied_by_long (G : Type*) [Magma G] : AssociativeTheory221_long G -> AssociativeTheory221 G :=
fun ⟨_, h4276, h4290, h4291, _, h4512⟩ => ⟨h4276, h4290, h4291, h4512⟩

theorem AT221_equiv (G : Type*) [Magma G] : AssociativeTheory221 G <-> AssociativeTheory221_long G :=
Iff.intro (AT221_implies_long G) (AT221_implied_by_long G)

theorem AT222_implies_long (G : Type*) [Magma G] (h : AssociativeTheory222 G) : AssociativeTheory222_long G := by
  obtain ⟨eq4293, eq4512⟩ := h
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  exact ⟨eq1, eq4293, eq4512⟩

theorem AT222_implied_by_long (G : Type*) [Magma G] : AssociativeTheory222_long G -> AssociativeTheory222 G :=
fun ⟨_, h4293, h4512⟩ => ⟨h4293, h4512⟩

theorem AT222_equiv (G : Type*) [Magma G] : AssociativeTheory222 G <-> AssociativeTheory222_long G :=
Iff.intro (AT222_implies_long G) (AT222_implied_by_long G)

theorem AT223_implies_long (G : Type*) [Magma G] (h : AssociativeTheory223 G) : AssociativeTheory223_long G := by
  obtain ⟨eq307, eq4293, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4293, eq4512⟩

theorem AT223_implied_by_long (G : Type*) [Magma G] : AssociativeTheory223_long G -> AssociativeTheory223 G :=
fun ⟨_, h307, _, h4293, h4512⟩ => ⟨h307, h4293, h4512⟩

theorem AT223_equiv (G : Type*) [Magma G] : AssociativeTheory223 G <-> AssociativeTheory223_long G :=
Iff.intro (AT223_implies_long G) (AT223_implied_by_long G)

theorem AT224_implies_long (G : Type*) [Magma G] (h : AssociativeTheory224 G) : AssociativeTheory224_long G := by
  obtain ⟨eq4269, eq4293, eq4512⟩ := h
  have eq4273 := Equation4269_4293_4512_implies_Equation4273 G eq4269 eq4293 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4293, eq4321, eq4512⟩

theorem AT224_implied_by_long (G : Type*) [Magma G] : AssociativeTheory224_long G -> AssociativeTheory224 G :=
fun ⟨_, h4269, _, _, _, h4293, _, h4512⟩ => ⟨h4269, h4293, h4512⟩

theorem AT224_equiv (G : Type*) [Magma G] : AssociativeTheory224 G <-> AssociativeTheory224_long G :=
Iff.intro (AT224_implies_long G) (AT224_implied_by_long G)

theorem AT225_implies_long (G : Type*) [Magma G] (h : AssociativeTheory225 G) : AssociativeTheory225_long G := by
  obtain ⟨eq4270, eq4293, eq4512⟩ := h
  have eq4272 := Equation4270_4293_4512_implies_Equation4272 G eq4270 eq4293 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4293, eq4343, eq4512⟩

theorem AT225_implied_by_long (G : Type*) [Magma G] : AssociativeTheory225_long G -> AssociativeTheory225 G :=
fun ⟨_, h4270, _, _, _, h4293, _, h4512⟩ => ⟨h4270, h4293, h4512⟩

theorem AT225_equiv (G : Type*) [Magma G] : AssociativeTheory225 G <-> AssociativeTheory225_long G :=
Iff.intro (AT225_implies_long G) (AT225_implied_by_long G)

theorem AT226_implies_long (G : Type*) [Magma G] (h : AssociativeTheory226 G) : AssociativeTheory226_long G := by
  obtain ⟨eq4269, eq4270, eq4293, eq4512⟩ := h
  have eq4273 := Equation4269_4293_4512_implies_Equation4273 G eq4269 eq4293 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4272 := Equation4270_4293_4512_implies_Equation4272 G eq4270 eq4293 eq4512
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4269, eq4270, eq4272, eq4273, eq4276, eq4279, eq4280, eq4293, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4512⟩

theorem AT226_implied_by_long (G : Type*) [Magma G] : AssociativeTheory226_long G -> AssociativeTheory226 G :=
fun ⟨_, h4269, h4270, _, _, _, _, _, h4293, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4269, h4270, h4293, h4512⟩

theorem AT226_equiv (G : Type*) [Magma G] : AssociativeTheory226 G <-> AssociativeTheory226_long G :=
Iff.intro (AT226_implies_long G) (AT226_implied_by_long G)

theorem AT227_implies_long (G : Type*) [Magma G] (h : AssociativeTheory227 G) : AssociativeTheory227_long G := by
  obtain ⟨eq4276, eq4293, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4512⟩

theorem AT227_implied_by_long (G : Type*) [Magma G] : AssociativeTheory227_long G -> AssociativeTheory227 G :=
fun ⟨_, h4276, h4293, h4512⟩ => ⟨h4276, h4293, h4512⟩

theorem AT227_equiv (G : Type*) [Magma G] : AssociativeTheory227 G <-> AssociativeTheory227_long G :=
Iff.intro (AT227_implies_long G) (AT227_implied_by_long G)

theorem AT228_implies_long (G : Type*) [Magma G] (h : AssociativeTheory228 G) : AssociativeTheory228_long G := by
  obtain ⟨eq4300, eq4512⟩ := h
  have eq1 := Equation4300_4512_implies_Equation1 G eq4300 eq4512
  have eq4272 := Equation4300_4512_implies_Equation4272 G eq4300 eq4512
  have eq4291 := Equation4300_4512_implies_Equation4291 G eq4300 eq4512
  exact ⟨eq1, eq4272, eq4291, eq4300, eq4512⟩

theorem AT228_implied_by_long (G : Type*) [Magma G] : AssociativeTheory228_long G -> AssociativeTheory228 G :=
fun ⟨_, _, _, h4300, h4512⟩ => ⟨h4300, h4512⟩

theorem AT228_equiv (G : Type*) [Magma G] : AssociativeTheory228 G <-> AssociativeTheory228_long G :=
Iff.intro (AT228_implies_long G) (AT228_implied_by_long G)

theorem AT229_implies_long (G : Type*) [Magma G] (h : AssociativeTheory229 G) : AssociativeTheory229_long G := by
  obtain ⟨eq307, eq4300, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4272 := Equation4300_4512_implies_Equation4272 G eq4300 eq4512
  have eq4291 := Equation4300_4512_implies_Equation4291 G eq4300 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact ⟨eq1, eq307, eq312, eq3253, eq3258, eq3278, eq4272, eq4291, eq4300, eq4512⟩

theorem AT229_implied_by_long (G : Type*) [Magma G] : AssociativeTheory229_long G -> AssociativeTheory229 G :=
fun ⟨_, h307, _, _, _, _, _, _, h4300, h4512⟩ => ⟨h307, h4300, h4512⟩

theorem AT229_equiv (G : Type*) [Magma G] : AssociativeTheory229 G <-> AssociativeTheory229_long G :=
Iff.intro (AT229_implies_long G) (AT229_implied_by_long G)

theorem AT230_implies_long (G : Type*) [Magma G] (h : AssociativeTheory230 G) : AssociativeTheory230_long G := by
  obtain ⟨eq4314, eq4512⟩ := h
  have eq1 := Equation4314_4512_implies_Equation1 G eq4314 eq4512
  exact ⟨eq1, eq4314, eq4512⟩

theorem AT230_implied_by_long (G : Type*) [Magma G] : AssociativeTheory230_long G -> AssociativeTheory230 G :=
fun ⟨_, h4314, h4512⟩ => ⟨h4314, h4512⟩

theorem AT230_equiv (G : Type*) [Magma G] : AssociativeTheory230 G <-> AssociativeTheory230_long G :=
Iff.intro (AT230_implies_long G) (AT230_implied_by_long G)

theorem AT231_implies_long (G : Type*) [Magma G] (h : AssociativeTheory231 G) : AssociativeTheory231_long G := by
  obtain ⟨eq307, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4314, eq4512⟩

theorem AT231_implied_by_long (G : Type*) [Magma G] : AssociativeTheory231_long G -> AssociativeTheory231 G :=
fun ⟨_, h307, _, h4314, h4512⟩ => ⟨h307, h4314, h4512⟩

theorem AT231_equiv (G : Type*) [Magma G] : AssociativeTheory231 G <-> AssociativeTheory231_long G :=
Iff.intro (AT231_implies_long G) (AT231_implied_by_long G)

theorem AT232_implies_long (G : Type*) [Magma G] (h : AssociativeTheory232 G) : AssociativeTheory232_long G := by
  obtain ⟨eq308, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation308_4512_implies_Equation307 G eq308 eq4512
  have eq3253 := Equation308_4512_implies_Equation3253 G eq308 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  exact ⟨eq1, eq307, eq308, eq3253, eq3255, eq3256, eq4268, eq4314, eq4512⟩

theorem AT232_implied_by_long (G : Type*) [Magma G] : AssociativeTheory232_long G -> AssociativeTheory232 G :=
fun ⟨_, _, h308, _, _, _, _, h4314, h4512⟩ => ⟨h308, h4314, h4512⟩

theorem AT232_equiv (G : Type*) [Magma G] : AssociativeTheory232 G <-> AssociativeTheory232_long G :=
Iff.intro (AT232_implies_long G) (AT232_implied_by_long G)

theorem AT233_implies_long (G : Type*) [Magma G] (h : AssociativeTheory233 G) : AssociativeTheory233_long G := by
  obtain ⟨eq323, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4314, eq4512⟩

theorem AT233_implied_by_long (G : Type*) [Magma G] : AssociativeTheory233_long G -> AssociativeTheory233 G :=
fun ⟨_, _, h323, _, _, h4314, h4512⟩ => ⟨h323, h4314, h4512⟩

theorem AT233_equiv (G : Type*) [Magma G] : AssociativeTheory233 G <-> AssociativeTheory233_long G :=
Iff.intro (AT233_implies_long G) (AT233_implied_by_long G)

theorem AT234_implies_long (G : Type*) [Magma G] (h : AssociativeTheory234 G) : AssociativeTheory234_long G := by
  obtain ⟨eq4268, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4268, eq4314, eq4512⟩

theorem AT234_implied_by_long (G : Type*) [Magma G] : AssociativeTheory234_long G -> AssociativeTheory234 G :=
fun ⟨_, h4268, h4314, h4512⟩ => ⟨h4268, h4314, h4512⟩

theorem AT234_equiv (G : Type*) [Magma G] : AssociativeTheory234 G <-> AssociativeTheory234_long G :=
Iff.intro (AT234_implies_long G) (AT234_implied_by_long G)

theorem AT235_implies_long (G : Type*) [Magma G] (h : AssociativeTheory235 G) : AssociativeTheory235_long G := by
  obtain ⟨eq4275, eq4314, eq4512⟩ := h
  have eq4268 := Equation4275_4314_4512_implies_Equation4268 G eq4275 eq4314 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4314, eq4512⟩

theorem AT235_implied_by_long (G : Type*) [Magma G] : AssociativeTheory235_long G -> AssociativeTheory235 G :=
fun ⟨_, _, h4275, _, _, _, h4314, h4512⟩ => ⟨h4275, h4314, h4512⟩

theorem AT235_equiv (G : Type*) [Magma G] : AssociativeTheory235 G <-> AssociativeTheory235_long G :=
Iff.intro (AT235_implies_long G) (AT235_implied_by_long G)

theorem AT236_implies_long (G : Type*) [Magma G] (h : AssociativeTheory236 G) : AssociativeTheory236_long G := by
  obtain ⟨eq4276, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4314, eq4512⟩

theorem AT236_implied_by_long (G : Type*) [Magma G] : AssociativeTheory236_long G -> AssociativeTheory236 G :=
fun ⟨_, h4276, h4314, h4512⟩ => ⟨h4276, h4314, h4512⟩

theorem AT236_equiv (G : Type*) [Magma G] : AssociativeTheory236 G <-> AssociativeTheory236_long G :=
Iff.intro (AT236_implies_long G) (AT236_implied_by_long G)

theorem AT237_implies_long (G : Type*) [Magma G] (h : AssociativeTheory237 G) : AssociativeTheory237_long G := by
  obtain ⟨eq4293, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4314, eq4512⟩

theorem AT237_implied_by_long (G : Type*) [Magma G] : AssociativeTheory237_long G -> AssociativeTheory237 G :=
fun ⟨_, h4293, h4314, h4512⟩ => ⟨h4293, h4314, h4512⟩

theorem AT237_equiv (G : Type*) [Magma G] : AssociativeTheory237 G <-> AssociativeTheory237_long G :=
Iff.intro (AT237_implies_long G) (AT237_implied_by_long G)

theorem AT238_implies_long (G : Type*) [Magma G] (h : AssociativeTheory238 G) : AssociativeTheory238_long G := by
  obtain ⟨eq4276, eq4293, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4314, eq4512⟩

theorem AT238_implied_by_long (G : Type*) [Magma G] : AssociativeTheory238_long G -> AssociativeTheory238 G :=
fun ⟨_, h4276, h4293, h4314, h4512⟩ => ⟨h4276, h4293, h4314, h4512⟩

theorem AT238_equiv (G : Type*) [Magma G] : AssociativeTheory238 G <-> AssociativeTheory238_long G :=
Iff.intro (AT238_implies_long G) (AT238_implied_by_long G)

theorem AT239_implies_long (G : Type*) [Magma G] (h : AssociativeTheory239 G) : AssociativeTheory239_long G := by
  obtain ⟨eq4315, eq4512⟩ := h
  have eq1 := Equation4315_4512_implies_Equation1 G eq4315 eq4512
  have eq4268 := Equation4315_4512_implies_Equation4268 G eq4315 eq4512
  have eq4314 := Equation4315_4512_implies_Equation4314 G eq4315 eq4512
  exact ⟨eq1, eq4268, eq4314, eq4315, eq4512⟩

theorem AT239_implied_by_long (G : Type*) [Magma G] : AssociativeTheory239_long G -> AssociativeTheory239 G :=
fun ⟨_, _, _, h4315, h4512⟩ => ⟨h4315, h4512⟩

theorem AT239_equiv (G : Type*) [Magma G] : AssociativeTheory239 G <-> AssociativeTheory239_long G :=
Iff.intro (AT239_implies_long G) (AT239_implied_by_long G)

theorem AT240_implies_long (G : Type*) [Magma G] (h : AssociativeTheory240 G) : AssociativeTheory240_long G := by
  obtain ⟨eq307, eq4315, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4268 := Equation4315_4512_implies_Equation4268 G eq4315 eq4512
  have eq4314 := Equation4315_4512_implies_Equation4314 G eq4315 eq4512
  have eq308 := Equation307_4268_4512_implies_Equation308 G eq307 eq4268 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact ⟨eq1, eq307, eq308, eq3253, eq3255, eq3256, eq4268, eq4314, eq4315, eq4512⟩

theorem AT240_implied_by_long (G : Type*) [Magma G] : AssociativeTheory240_long G -> AssociativeTheory240 G :=
fun ⟨_, h307, _, _, _, _, _, _, h4315, h4512⟩ => ⟨h307, h4315, h4512⟩

theorem AT240_equiv (G : Type*) [Magma G] : AssociativeTheory240 G <-> AssociativeTheory240_long G :=
Iff.intro (AT240_implies_long G) (AT240_implied_by_long G)

theorem AT241_implies_long (G : Type*) [Magma G] (h : AssociativeTheory241 G) : AssociativeTheory241_long G := by
  obtain ⟨eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4320, eq4512⟩

theorem AT241_implied_by_long (G : Type*) [Magma G] : AssociativeTheory241_long G -> AssociativeTheory241 G :=
fun ⟨_, h4320, h4512⟩ => ⟨h4320, h4512⟩

theorem AT241_equiv (G : Type*) [Magma G] : AssociativeTheory241 G <-> AssociativeTheory241_long G :=
Iff.intro (AT241_implies_long G) (AT241_implied_by_long G)

theorem AT242_implies_long (G : Type*) [Magma G] (h : AssociativeTheory242 G) : AssociativeTheory242_long G := by
  obtain ⟨eq47, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq47, eq4320, eq4512⟩

theorem AT242_implied_by_long (G : Type*) [Magma G] : AssociativeTheory242_long G -> AssociativeTheory242 G :=
fun ⟨_, h47, h4320, h4512⟩ => ⟨h47, h4320, h4512⟩

theorem AT242_equiv (G : Type*) [Magma G] : AssociativeTheory242 G <-> AssociativeTheory242_long G :=
Iff.intro (AT242_implies_long G) (AT242_implied_by_long G)

theorem AT243_implies_long (G : Type*) [Magma G] (h : AssociativeTheory243 G) : AssociativeTheory243_long G := by
  obtain ⟨eq75, eq4320, eq4512⟩ := h
  have eq4362 := Equation75_4320_4512_implies_Equation4362 G eq75 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq47 := Equation75_4512_implies_Equation47 G eq75 eq4512
  exact ⟨eq1, eq47, eq75, eq4320, eq4362, eq4512⟩

theorem AT243_implied_by_long (G : Type*) [Magma G] : AssociativeTheory243_long G -> AssociativeTheory243 G :=
fun ⟨_, _, h75, h4320, _, h4512⟩ => ⟨h75, h4320, h4512⟩

theorem AT243_equiv (G : Type*) [Magma G] : AssociativeTheory243 G <-> AssociativeTheory243_long G :=
Iff.intro (AT243_implies_long G) (AT243_implied_by_long G)

theorem AT244_implies_long (G : Type*) [Magma G] (h : AssociativeTheory244 G) : AssociativeTheory244_long G := by
  obtain ⟨eq307, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4320, eq4512⟩

theorem AT244_implied_by_long (G : Type*) [Magma G] : AssociativeTheory244_long G -> AssociativeTheory244 G :=
fun ⟨_, h307, _, h4320, h4512⟩ => ⟨h307, h4320, h4512⟩

theorem AT244_equiv (G : Type*) [Magma G] : AssociativeTheory244 G <-> AssociativeTheory244_long G :=
Iff.intro (AT244_implies_long G) (AT244_implied_by_long G)

theorem AT245_implies_long (G : Type*) [Magma G] (h : AssociativeTheory245 G) : AssociativeTheory245_long G := by
  obtain ⟨eq323, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4320, eq4512⟩

theorem AT245_implied_by_long (G : Type*) [Magma G] : AssociativeTheory245_long G -> AssociativeTheory245 G :=
fun ⟨_, _, h323, _, _, h4320, h4512⟩ => ⟨h323, h4320, h4512⟩

theorem AT245_equiv (G : Type*) [Magma G] : AssociativeTheory245 G <-> AssociativeTheory245_long G :=
Iff.intro (AT245_implies_long G) (AT245_implied_by_long G)

theorem AT246_implies_long (G : Type*) [Magma G] (h : AssociativeTheory246 G) : AssociativeTheory246_long G := by
  obtain ⟨eq411, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq411, eq4320, eq4512⟩

theorem AT246_implied_by_long (G : Type*) [Magma G] : AssociativeTheory246_long G -> AssociativeTheory246 G :=
fun ⟨_, h411, h4320, h4512⟩ => ⟨h411, h4320, h4512⟩

theorem AT246_equiv (G : Type*) [Magma G] : AssociativeTheory246 G <-> AssociativeTheory246_long G :=
Iff.intro (AT246_implies_long G) (AT246_implied_by_long G)

theorem AT247_implies_long (G : Type*) [Magma G] (h : AssociativeTheory247 G) : AssociativeTheory247_long G := by
  obtain ⟨eq513, eq4320, eq4512⟩ := h
  have eq4362 := Equation513_4320_4512_implies_Equation4362 G eq513 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq411 := Equation513_4512_implies_Equation411 G eq513 eq4512
  exact ⟨eq1, eq411, eq513, eq4320, eq4362, eq4512⟩

theorem AT247_implied_by_long (G : Type*) [Magma G] : AssociativeTheory247_long G -> AssociativeTheory247 G :=
fun ⟨_, _, h513, h4320, _, h4512⟩ => ⟨h513, h4320, h4512⟩

theorem AT247_equiv (G : Type*) [Magma G] : AssociativeTheory247 G <-> AssociativeTheory247_long G :=
Iff.intro (AT247_implies_long G) (AT247_implied_by_long G)

theorem AT248_implies_long (G : Type*) [Magma G] (h : AssociativeTheory248 G) : AssociativeTheory248_long G := by
  obtain ⟨eq3253, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq3253, eq4320, eq4512⟩

theorem AT248_implied_by_long (G : Type*) [Magma G] : AssociativeTheory248_long G -> AssociativeTheory248 G :=
fun ⟨_, h3253, h4320, h4512⟩ => ⟨h3253, h4320, h4512⟩

theorem AT248_equiv (G : Type*) [Magma G] : AssociativeTheory248 G <-> AssociativeTheory248_long G :=
Iff.intro (AT248_implies_long G) (AT248_implied_by_long G)

theorem AT249_implies_long (G : Type*) [Magma G] (h : AssociativeTheory249 G) : AssociativeTheory249_long G := by
  obtain ⟨eq3261, eq4320, eq4512⟩ := h
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq4275, eq4320, eq4512⟩

theorem AT249_implied_by_long (G : Type*) [Magma G] : AssociativeTheory249_long G -> AssociativeTheory249 G :=
fun ⟨_, _, h3261, _, _, _, h4320, h4512⟩ => ⟨h3261, h4320, h4512⟩

theorem AT249_equiv (G : Type*) [Magma G] : AssociativeTheory249 G <-> AssociativeTheory249_long G :=
Iff.intro (AT249_implies_long G) (AT249_implied_by_long G)

theorem AT250_implies_long (G : Type*) [Magma G] (h : AssociativeTheory250 G) : AssociativeTheory250_long G := by
  obtain ⟨eq3306, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact ⟨eq1, eq3253, eq3306, eq4320, eq4512⟩

theorem AT250_implied_by_long (G : Type*) [Magma G] : AssociativeTheory250_long G -> AssociativeTheory250 G :=
fun ⟨_, _, h3306, h4320, h4512⟩ => ⟨h3306, h4320, h4512⟩

theorem AT250_equiv (G : Type*) [Magma G] : AssociativeTheory250 G <-> AssociativeTheory250_long G :=
Iff.intro (AT250_implies_long G) (AT250_implied_by_long G)

theorem AT251_implies_long (G : Type*) [Magma G] (h : AssociativeTheory251 G) : AssociativeTheory251_long G := by
  obtain ⟨eq4268, eq4320, eq4512⟩ := h
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4320, eq4512⟩

theorem AT251_implied_by_long (G : Type*) [Magma G] : AssociativeTheory251_long G -> AssociativeTheory251 G :=
fun ⟨_, h4268, _, _, _, _, h4320, h4512⟩ => ⟨h4268, h4320, h4512⟩

theorem AT251_equiv (G : Type*) [Magma G] : AssociativeTheory251 G <-> AssociativeTheory251_long G :=
Iff.intro (AT251_implies_long G) (AT251_implied_by_long G)

theorem AT252_implies_long (G : Type*) [Magma G] (h : AssociativeTheory252 G) : AssociativeTheory252_long G := by
  obtain ⟨eq4275, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4275, eq4320, eq4512⟩

theorem AT252_implied_by_long (G : Type*) [Magma G] : AssociativeTheory252_long G -> AssociativeTheory252 G :=
fun ⟨_, h4275, h4320, h4512⟩ => ⟨h4275, h4320, h4512⟩

theorem AT252_equiv (G : Type*) [Magma G] : AssociativeTheory252 G <-> AssociativeTheory252_long G :=
Iff.intro (AT252_implies_long G) (AT252_implied_by_long G)

theorem AT253_implies_long (G : Type*) [Magma G] (h : AssociativeTheory253 G) : AssociativeTheory253_long G := by
  obtain ⟨eq4276, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4320, eq4512⟩

theorem AT253_implied_by_long (G : Type*) [Magma G] : AssociativeTheory253_long G -> AssociativeTheory253 G :=
fun ⟨_, h4276, h4320, h4512⟩ => ⟨h4276, h4320, h4512⟩

theorem AT253_equiv (G : Type*) [Magma G] : AssociativeTheory253 G <-> AssociativeTheory253_long G :=
Iff.intro (AT253_implies_long G) (AT253_implied_by_long G)

theorem AT254_implies_long (G : Type*) [Magma G] (h : AssociativeTheory254 G) : AssociativeTheory254_long G := by
  obtain ⟨eq4293, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4293, eq4320, eq4512⟩

theorem AT254_implied_by_long (G : Type*) [Magma G] : AssociativeTheory254_long G -> AssociativeTheory254 G :=
fun ⟨_, h4293, h4320, h4512⟩ => ⟨h4293, h4320, h4512⟩

theorem AT254_equiv (G : Type*) [Magma G] : AssociativeTheory254 G <-> AssociativeTheory254_long G :=
Iff.intro (AT254_implies_long G) (AT254_implied_by_long G)

theorem AT255_implies_long (G : Type*) [Magma G] (h : AssociativeTheory255 G) : AssociativeTheory255_long G := by
  obtain ⟨eq4276, eq4293, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4320, eq4512⟩

theorem AT255_implied_by_long (G : Type*) [Magma G] : AssociativeTheory255_long G -> AssociativeTheory255 G :=
fun ⟨_, h4276, h4293, h4320, h4512⟩ => ⟨h4276, h4293, h4320, h4512⟩

theorem AT255_equiv (G : Type*) [Magma G] : AssociativeTheory255 G <-> AssociativeTheory255_long G :=
Iff.intro (AT255_implies_long G) (AT255_implied_by_long G)

theorem AT256_implies_long (G : Type*) [Magma G] (h : AssociativeTheory256 G) : AssociativeTheory256_long G := by
  obtain ⟨eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT256_implied_by_long (G : Type*) [Magma G] : AssociativeTheory256_long G -> AssociativeTheory256 G :=
fun ⟨_, h4314, h4320, _, _, h4512⟩ => ⟨h4314, h4320, h4512⟩

theorem AT256_equiv (G : Type*) [Magma G] : AssociativeTheory256 G <-> AssociativeTheory256_long G :=
Iff.intro (AT256_implies_long G) (AT256_implied_by_long G)

theorem AT257_implies_long (G : Type*) [Magma G] (h : AssociativeTheory257 G) : AssociativeTheory257_long G := by
  obtain ⟨eq307, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT257_implied_by_long (G : Type*) [Magma G] : AssociativeTheory257_long G -> AssociativeTheory257 G :=
fun ⟨_, h307, _, h4314, h4320, _, _, h4512⟩ => ⟨h307, h4314, h4320, h4512⟩

theorem AT257_equiv (G : Type*) [Magma G] : AssociativeTheory257 G <-> AssociativeTheory257_long G :=
Iff.intro (AT257_implies_long G) (AT257_implied_by_long G)

theorem AT258_implies_long (G : Type*) [Magma G] (h : AssociativeTheory258 G) : AssociativeTheory258_long G := by
  obtain ⟨eq323, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq4362 := Equation323_4321_4512_implies_Equation4362 G eq323 eq4321 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT258_implied_by_long (G : Type*) [Magma G] : AssociativeTheory258_long G -> AssociativeTheory258 G :=
fun ⟨_, _, h323, _, _, h4314, h4320, _, _, _, h4512⟩ => ⟨h323, h4314, h4320, h4512⟩

theorem AT258_equiv (G : Type*) [Magma G] : AssociativeTheory258 G <-> AssociativeTheory258_long G :=
Iff.intro (AT258_implies_long G) (AT258_implied_by_long G)

theorem AT259_implies_long (G : Type*) [Magma G] (h : AssociativeTheory259 G) : AssociativeTheory259_long G := by
  obtain ⟨eq4268, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT259_implied_by_long (G : Type*) [Magma G] : AssociativeTheory259_long G -> AssociativeTheory259 G :=
fun ⟨_, h4268, _, _, _, _, h4314, h4320, _, _, h4512⟩ => ⟨h4268, h4314, h4320, h4512⟩

theorem AT259_equiv (G : Type*) [Magma G] : AssociativeTheory259 G <-> AssociativeTheory259_long G :=
Iff.intro (AT259_implies_long G) (AT259_implied_by_long G)

theorem AT260_implies_long (G : Type*) [Magma G] (h : AssociativeTheory260 G) : AssociativeTheory260_long G := by
  obtain ⟨eq4276, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT260_implied_by_long (G : Type*) [Magma G] : AssociativeTheory260_long G -> AssociativeTheory260 G :=
fun ⟨_, h4276, h4314, h4320, _, _, h4512⟩ => ⟨h4276, h4314, h4320, h4512⟩

theorem AT260_equiv (G : Type*) [Magma G] : AssociativeTheory260 G <-> AssociativeTheory260_long G :=
Iff.intro (AT260_implies_long G) (AT260_implied_by_long G)

theorem AT261_implies_long (G : Type*) [Magma G] (h : AssociativeTheory261 G) : AssociativeTheory261_long G := by
  obtain ⟨eq4293, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT261_implied_by_long (G : Type*) [Magma G] : AssociativeTheory261_long G -> AssociativeTheory261 G :=
fun ⟨_, h4293, h4314, h4320, _, _, h4512⟩ => ⟨h4293, h4314, h4320, h4512⟩

theorem AT261_equiv (G : Type*) [Magma G] : AssociativeTheory261 G <-> AssociativeTheory261_long G :=
Iff.intro (AT261_implies_long G) (AT261_implied_by_long G)

theorem AT262_implies_long (G : Type*) [Magma G] (h : AssociativeTheory262 G) : AssociativeTheory262_long G := by
  obtain ⟨eq4276, eq4293, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem AT262_implied_by_long (G : Type*) [Magma G] : AssociativeTheory262_long G -> AssociativeTheory262 G :=
fun ⟨_, h4276, h4293, h4314, h4320, _, _, h4512⟩ => ⟨h4276, h4293, h4314, h4320, h4512⟩

theorem AT262_equiv (G : Type*) [Magma G] : AssociativeTheory262 G <-> AssociativeTheory262_long G :=
Iff.intro (AT262_implies_long G) (AT262_implied_by_long G)

theorem AT263_implies_long (G : Type*) [Magma G] (h : AssociativeTheory263 G) : AssociativeTheory263_long G := by
  obtain ⟨eq4321, eq4512⟩ := h
  have eq1 := Equation4321_4512_implies_Equation1 G eq4321 eq4512
  exact ⟨eq1, eq4321, eq4512⟩

theorem AT263_implied_by_long (G : Type*) [Magma G] : AssociativeTheory263_long G -> AssociativeTheory263 G :=
fun ⟨_, h4321, h4512⟩ => ⟨h4321, h4512⟩

theorem AT263_equiv (G : Type*) [Magma G] : AssociativeTheory263 G <-> AssociativeTheory263_long G :=
Iff.intro (AT263_implies_long G) (AT263_implied_by_long G)

theorem AT264_implies_long (G : Type*) [Magma G] (h : AssociativeTheory264 G) : AssociativeTheory264_long G := by
  obtain ⟨eq40, eq4321, eq4512⟩ := h
  have eq3264 := Equation40_4321_4512_implies_Equation3264 G eq40 eq4321 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq4268 := Equation4270_4284_4512_implies_Equation4268 G eq4270 eq4284 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq310 := Equation3275_4512_implies_Equation310 G eq3275 eq4512
  have eq315 := Equation3275_4512_implies_Equation315 G eq3275 eq4512
  have eq4276 := Equation3275_4512_implies_Equation4276 G eq3275 eq4512
  have eq4277 := Equation3275_4512_implies_Equation4277 G eq3275 eq4512
  have eq4280 := Equation3275_4512_implies_Equation4280 G eq3275 eq4512
  have eq4288 := Equation3275_4512_implies_Equation4288 G eq3275 eq4512
  have eq4299 := Equation3275_4512_implies_Equation4299 G eq3275 eq4512
  have eq4304 := Equation3275_4512_implies_Equation4304 G eq3275 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3264, eq3271, eq3275, eq3278, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4512⟩

theorem AT264_implied_by_long (G : Type*) [Magma G] : AssociativeTheory264_long G -> AssociativeTheory264 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h40, h4321, h4512⟩

theorem AT264_equiv (G : Type*) [Magma G] : AssociativeTheory264 G <-> AssociativeTheory264_long G :=
Iff.intro (AT264_implies_long G) (AT264_implied_by_long G)

theorem AT265_implies_long (G : Type*) [Magma G] (h : AssociativeTheory265 G) : AssociativeTheory265_long G := by
  obtain ⟨eq307, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4321, eq4512⟩

theorem AT265_implied_by_long (G : Type*) [Magma G] : AssociativeTheory265_long G -> AssociativeTheory265 G :=
fun ⟨_, h307, _, h4321, h4512⟩ => ⟨h307, h4321, h4512⟩

theorem AT265_equiv (G : Type*) [Magma G] : AssociativeTheory265 G <-> AssociativeTheory265_long G :=
Iff.intro (AT265_implies_long G) (AT265_implied_by_long G)

theorem AT266_implies_long (G : Type*) [Magma G] (h : AssociativeTheory266 G) : AssociativeTheory266_long G := by
  obtain ⟨eq3260, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3260_4512_implies_Equation307 G eq3260 eq4512
  have eq308 := Equation3260_4512_implies_Equation308 G eq3260 eq4512
  have eq310 := Equation3260_4512_implies_Equation310 G eq3260 eq4512
  have eq3253 := Equation3260_4512_implies_Equation3253 G eq3260 eq4512
  have eq3255 := Equation3260_4512_implies_Equation3255 G eq3260 eq4512
  have eq3256 := Equation3260_4512_implies_Equation3256 G eq3260 eq4512
  have eq3258 := Equation3260_4512_implies_Equation3258 G eq3260 eq4512
  have eq3259 := Equation3260_4512_implies_Equation3259 G eq3260 eq4512
  have eq3261 := Equation3260_4512_implies_Equation3261 G eq3260 eq4512
  have eq4268 := Equation3260_4512_implies_Equation4268 G eq3260 eq4512
  have eq4270 := Equation3260_4512_implies_Equation4270 G eq3260 eq4512
  have eq4284 := Equation3260_4512_implies_Equation4284 G eq3260 eq4512
  have eq4288 := Equation3260_4512_implies_Equation4288 G eq3260 eq4512
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq40 := Equation3255_4321_4512_implies_Equation40 G eq3255 eq4321 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3264 := Equation40_4321_4512_implies_Equation3264 G eq40 eq4321 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3271, eq3273, eq3275, eq3278, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4512⟩

theorem AT266_implied_by_long (G : Type*) [Magma G] : AssociativeTheory266_long G -> AssociativeTheory266 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3260, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3260, h4321, h4512⟩

theorem AT266_equiv (G : Type*) [Magma G] : AssociativeTheory266 G <-> AssociativeTheory266_long G :=
Iff.intro (AT266_implies_long G) (AT266_implied_by_long G)

theorem AT267_implies_long (G : Type*) [Magma G] (h : AssociativeTheory267 G) : AssociativeTheory267_long G := by
  obtain ⟨eq3265, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3253 := Equation3265_4512_implies_Equation3253 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq3261 := Equation3265_4512_implies_Equation3261 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq40 := Equation3255_4321_4512_implies_Equation40 G eq3255 eq4321 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3264 := Equation40_4321_4512_implies_Equation3264 G eq40 eq4321 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3261, eq3264, eq3265, eq3271, eq3274, eq3275, eq3278, eq3290, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4512⟩

theorem AT267_implied_by_long (G : Type*) [Magma G] : AssociativeTheory267_long G -> AssociativeTheory267 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3265, h4321, h4512⟩

theorem AT267_equiv (G : Type*) [Magma G] : AssociativeTheory267 G <-> AssociativeTheory267_long G :=
Iff.intro (AT267_implies_long G) (AT267_implied_by_long G)

theorem AT268_implies_long (G : Type*) [Magma G] (h : AssociativeTheory268 G) : AssociativeTheory268_long G := by
  obtain ⟨eq3260, eq3265, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3265_4512_implies_Equation307 G eq3265 eq4512
  have eq308 := Equation3265_4512_implies_Equation308 G eq3265 eq4512
  have eq310 := Equation3265_4512_implies_Equation310 G eq3265 eq4512
  have eq3253 := Equation3265_4512_implies_Equation3253 G eq3265 eq4512
  have eq3255 := Equation3265_4512_implies_Equation3255 G eq3265 eq4512
  have eq3256 := Equation3265_4512_implies_Equation3256 G eq3265 eq4512
  have eq3258 := Equation3265_4512_implies_Equation3258 G eq3265 eq4512
  have eq3259 := Equation3265_4512_implies_Equation3259 G eq3265 eq4512
  have eq3261 := Equation3265_4512_implies_Equation3261 G eq3265 eq4512
  have eq4268 := Equation3265_4512_implies_Equation4268 G eq3265 eq4512
  have eq4270 := Equation3265_4512_implies_Equation4270 G eq3265 eq4512
  have eq4284 := Equation3265_4512_implies_Equation4284 G eq3265 eq4512
  have eq4288 := Equation3265_4512_implies_Equation4288 G eq3265 eq4512
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq40 := Equation3255_4321_4512_implies_Equation40 G eq3255 eq4321 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3264 := Equation40_4321_4512_implies_Equation3264 G eq40 eq4321 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4512⟩

theorem AT268_implied_by_long (G : Type*) [Magma G] : AssociativeTheory268_long G -> AssociativeTheory268 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3260, _, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3260, h3265, h4321, h4512⟩

theorem AT268_equiv (G : Type*) [Magma G] : AssociativeTheory268 G <-> AssociativeTheory268_long G :=
Iff.intro (AT268_implies_long G) (AT268_implied_by_long G)

theorem AT269_implies_long (G : Type*) [Magma G] (h : AssociativeTheory269 G) : AssociativeTheory269_long G := by
  obtain ⟨eq3267, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq40 := Equation3255_4321_4512_implies_Equation40 G eq3255 eq4321 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq3274 := Equation3277_4512_implies_Equation3274 G eq3277 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4512⟩

theorem AT269_implied_by_long (G : Type*) [Magma G] : AssociativeTheory269_long G -> AssociativeTheory269 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3267, h4321, h4512⟩

theorem AT269_equiv (G : Type*) [Magma G] : AssociativeTheory269 G <-> AssociativeTheory269_long G :=
Iff.intro (AT269_implies_long G) (AT269_implied_by_long G)

theorem AT270_implies_long (G : Type*) [Magma G] (h : AssociativeTheory270 G) : AssociativeTheory270_long G := by
  obtain ⟨eq4268, eq4321, eq4512⟩ := h
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4321, eq4512⟩

theorem AT270_implied_by_long (G : Type*) [Magma G] : AssociativeTheory270_long G -> AssociativeTheory270 G :=
fun ⟨_, h4268, _, _, _, _, h4321, h4512⟩ => ⟨h4268, h4321, h4512⟩

theorem AT270_equiv (G : Type*) [Magma G] : AssociativeTheory270 G <-> AssociativeTheory270_long G :=
Iff.intro (AT270_implies_long G) (AT270_implied_by_long G)

theorem AT271_implies_long (G : Type*) [Magma G] (h : AssociativeTheory271 G) : AssociativeTheory271_long G := by
  obtain ⟨eq4270, eq4321, eq4512⟩ := h
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4321, eq4343, eq4512⟩

theorem AT271_implied_by_long (G : Type*) [Magma G] : AssociativeTheory271_long G -> AssociativeTheory271 G :=
fun ⟨_, h4270, _, _, _, h4321, _, h4512⟩ => ⟨h4270, h4321, h4512⟩

theorem AT271_equiv (G : Type*) [Magma G] : AssociativeTheory271 G <-> AssociativeTheory271_long G :=
Iff.intro (AT271_implies_long G) (AT271_implied_by_long G)

theorem AT272_implies_long (G : Type*) [Magma G] (h : AssociativeTheory272 G) : AssociativeTheory272_long G := by
  obtain ⟨eq4268, eq4270, eq4321, eq4512⟩ := h
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  have eq4290 := Equation4297_4512_implies_Equation4290 G eq4297 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  exact ⟨eq1, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4512⟩

theorem AT272_implied_by_long (G : Type*) [Magma G] : AssociativeTheory272_long G -> AssociativeTheory272 G :=
fun ⟨_, h4268, h4270, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h4268, h4270, h4321, h4512⟩

theorem AT272_equiv (G : Type*) [Magma G] : AssociativeTheory272 G <-> AssociativeTheory272_long G :=
Iff.intro (AT272_implies_long G) (AT272_implied_by_long G)

theorem AT273_implies_long (G : Type*) [Magma G] (h : AssociativeTheory273 G) : AssociativeTheory273_long G := by
  obtain ⟨eq4276, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4321, eq4512⟩

theorem AT273_implied_by_long (G : Type*) [Magma G] : AssociativeTheory273_long G -> AssociativeTheory273 G :=
fun ⟨_, h4276, h4321, h4512⟩ => ⟨h4276, h4321, h4512⟩

theorem AT273_equiv (G : Type*) [Magma G] : AssociativeTheory273 G <-> AssociativeTheory273_long G :=
Iff.intro (AT273_implies_long G) (AT273_implied_by_long G)

theorem AT274_implies_long (G : Type*) [Magma G] (h : AssociativeTheory274 G) : AssociativeTheory274_long G := by
  obtain ⟨eq4284, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4321, eq4512⟩

theorem AT274_implied_by_long (G : Type*) [Magma G] : AssociativeTheory274_long G -> AssociativeTheory274 G :=
fun ⟨_, h4284, h4321, h4512⟩ => ⟨h4284, h4321, h4512⟩

theorem AT274_equiv (G : Type*) [Magma G] : AssociativeTheory274 G <-> AssociativeTheory274_long G :=
Iff.intro (AT274_implies_long G) (AT274_implied_by_long G)

theorem AT275_implies_long (G : Type*) [Magma G] (h : AssociativeTheory275 G) : AssociativeTheory275_long G := by
  obtain ⟨eq307, eq4284, eq4321, eq4512⟩ := h
  have eq4293 := Equation307_4284_4321_4512_implies_Equation4293 G eq307 eq4284 eq4321 eq4512
  have eq4290 := Equation4284_4293_4512_implies_Equation4290 G eq4284 eq4293 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem AT275_implied_by_long (G : Type*) [Magma G] : AssociativeTheory275_long G -> AssociativeTheory275 G :=
fun ⟨_, h307, _, h4284, _, _, h4321, _, h4512⟩ => ⟨h307, h4284, h4321, h4512⟩

theorem AT275_equiv (G : Type*) [Magma G] : AssociativeTheory275 G <-> AssociativeTheory275_long G :=
Iff.intro (AT275_implies_long G) (AT275_implied_by_long G)

theorem AT276_implies_long (G : Type*) [Magma G] (h : AssociativeTheory276 G) : AssociativeTheory276_long G := by
  obtain ⟨eq4276, eq4284, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4321, eq4512⟩

theorem AT276_implied_by_long (G : Type*) [Magma G] : AssociativeTheory276_long G -> AssociativeTheory276 G :=
fun ⟨_, h4276, h4284, h4321, h4512⟩ => ⟨h4276, h4284, h4321, h4512⟩

theorem AT276_equiv (G : Type*) [Magma G] : AssociativeTheory276 G <-> AssociativeTheory276_long G :=
Iff.intro (AT276_implies_long G) (AT276_implied_by_long G)

theorem AT277_implies_long (G : Type*) [Magma G] (h : AssociativeTheory277 G) : AssociativeTheory277_long G := by
  obtain ⟨eq4290, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4290, eq4321, eq4512⟩

theorem AT277_implied_by_long (G : Type*) [Magma G] : AssociativeTheory277_long G -> AssociativeTheory277 G :=
fun ⟨_, h4290, h4321, h4512⟩ => ⟨h4290, h4321, h4512⟩

theorem AT277_equiv (G : Type*) [Magma G] : AssociativeTheory277 G <-> AssociativeTheory277_long G :=
Iff.intro (AT277_implies_long G) (AT277_implied_by_long G)

theorem AT278_implies_long (G : Type*) [Magma G] (h : AssociativeTheory278 G) : AssociativeTheory278_long G := by
  obtain ⟨eq4276, eq4290, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4290, eq4321, eq4512⟩

theorem AT278_implied_by_long (G : Type*) [Magma G] : AssociativeTheory278_long G -> AssociativeTheory278 G :=
fun ⟨_, h4276, h4290, h4321, h4512⟩ => ⟨h4276, h4290, h4321, h4512⟩

theorem AT278_equiv (G : Type*) [Magma G] : AssociativeTheory278 G <-> AssociativeTheory278_long G :=
Iff.intro (AT278_implies_long G) (AT278_implied_by_long G)

theorem AT279_implies_long (G : Type*) [Magma G] (h : AssociativeTheory279 G) : AssociativeTheory279_long G := by
  obtain ⟨eq4284, eq4290, eq4321, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem AT279_implied_by_long (G : Type*) [Magma G] : AssociativeTheory279_long G -> AssociativeTheory279 G :=
fun ⟨_, h4284, h4290, _, h4321, _, h4512⟩ => ⟨h4284, h4290, h4321, h4512⟩

theorem AT279_equiv (G : Type*) [Magma G] : AssociativeTheory279 G <-> AssociativeTheory279_long G :=
Iff.intro (AT279_implies_long G) (AT279_implied_by_long G)

theorem AT280_implies_long (G : Type*) [Magma G] (h : AssociativeTheory280 G) : AssociativeTheory280_long G := by
  obtain ⟨eq4276, eq4284, eq4290, eq4321, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem AT280_implied_by_long (G : Type*) [Magma G] : AssociativeTheory280_long G -> AssociativeTheory280 G :=
fun ⟨_, h4276, h4284, h4290, _, h4321, _, h4512⟩ => ⟨h4276, h4284, h4290, h4321, h4512⟩

theorem AT280_equiv (G : Type*) [Magma G] : AssociativeTheory280 G <-> AssociativeTheory280_long G :=
Iff.intro (AT280_implies_long G) (AT280_implied_by_long G)

theorem AT281_implies_long (G : Type*) [Magma G] (h : AssociativeTheory281 G) : AssociativeTheory281_long G := by
  obtain ⟨eq4293, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4321, eq4512⟩

theorem AT281_implied_by_long (G : Type*) [Magma G] : AssociativeTheory281_long G -> AssociativeTheory281 G :=
fun ⟨_, h4293, h4321, h4512⟩ => ⟨h4293, h4321, h4512⟩

theorem AT281_equiv (G : Type*) [Magma G] : AssociativeTheory281 G <-> AssociativeTheory281_long G :=
Iff.intro (AT281_implies_long G) (AT281_implied_by_long G)

theorem AT282_implies_long (G : Type*) [Magma G] (h : AssociativeTheory282 G) : AssociativeTheory282_long G := by
  obtain ⟨eq307, eq4293, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4293, eq4321, eq4512⟩

theorem AT282_implied_by_long (G : Type*) [Magma G] : AssociativeTheory282_long G -> AssociativeTheory282 G :=
fun ⟨_, h307, _, h4293, h4321, h4512⟩ => ⟨h307, h4293, h4321, h4512⟩

theorem AT282_equiv (G : Type*) [Magma G] : AssociativeTheory282 G <-> AssociativeTheory282_long G :=
Iff.intro (AT282_implies_long G) (AT282_implied_by_long G)

theorem AT283_implies_long (G : Type*) [Magma G] (h : AssociativeTheory283 G) : AssociativeTheory283_long G := by
  obtain ⟨eq4270, eq4293, eq4321, eq4512⟩ := h
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4293, eq4321, eq4343, eq4512⟩

theorem AT283_implied_by_long (G : Type*) [Magma G] : AssociativeTheory283_long G -> AssociativeTheory283 G :=
fun ⟨_, h4270, _, _, _, h4293, h4321, _, h4512⟩ => ⟨h4270, h4293, h4321, h4512⟩

theorem AT283_equiv (G : Type*) [Magma G] : AssociativeTheory283 G <-> AssociativeTheory283_long G :=
Iff.intro (AT283_implies_long G) (AT283_implied_by_long G)

theorem AT284_implies_long (G : Type*) [Magma G] (h : AssociativeTheory284 G) : AssociativeTheory284_long G := by
  obtain ⟨eq4276, eq4293, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4321, eq4512⟩

theorem AT284_implied_by_long (G : Type*) [Magma G] : AssociativeTheory284_long G -> AssociativeTheory284 G :=
fun ⟨_, h4276, h4293, h4321, h4512⟩ => ⟨h4276, h4293, h4321, h4512⟩

theorem AT284_equiv (G : Type*) [Magma G] : AssociativeTheory284 G <-> AssociativeTheory284_long G :=
Iff.intro (AT284_implies_long G) (AT284_implied_by_long G)

theorem AT285_implies_long (G : Type*) [Magma G] (h : AssociativeTheory285 G) : AssociativeTheory285_long G := by
  obtain ⟨eq4343, eq4512⟩ := h
  have eq1 := Equation4343_4512_implies_Equation1 G eq4343 eq4512
  exact ⟨eq1, eq4343, eq4512⟩

theorem AT285_implied_by_long (G : Type*) [Magma G] : AssociativeTheory285_long G -> AssociativeTheory285 G :=
fun ⟨_, h4343, h4512⟩ => ⟨h4343, h4512⟩

theorem AT285_equiv (G : Type*) [Magma G] : AssociativeTheory285 G <-> AssociativeTheory285_long G :=
Iff.intro (AT285_implies_long G) (AT285_implied_by_long G)

theorem AT286_implies_long (G : Type*) [Magma G] (h : AssociativeTheory286 G) : AssociativeTheory286_long G := by
  obtain ⟨eq307, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4343, eq4512⟩

theorem AT286_implied_by_long (G : Type*) [Magma G] : AssociativeTheory286_long G -> AssociativeTheory286 G :=
fun ⟨_, h307, _, h4343, h4512⟩ => ⟨h307, h4343, h4512⟩

theorem AT286_equiv (G : Type*) [Magma G] : AssociativeTheory286 G <-> AssociativeTheory286_long G :=
Iff.intro (AT286_implies_long G) (AT286_implied_by_long G)

theorem AT287_implies_long (G : Type*) [Magma G] (h : AssociativeTheory287 G) : AssociativeTheory287_long G := by
  obtain ⟨eq4268, eq4343, eq4512⟩ := h
  have eq4275 := Equation4268_4343_4512_implies_Equation4275 G eq4268 eq4343 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4343, eq4512⟩

theorem AT287_implied_by_long (G : Type*) [Magma G] : AssociativeTheory287_long G -> AssociativeTheory287 G :=
fun ⟨_, h4268, _, _, _, _, h4343, h4512⟩ => ⟨h4268, h4343, h4512⟩

theorem AT287_equiv (G : Type*) [Magma G] : AssociativeTheory287 G <-> AssociativeTheory287_long G :=
Iff.intro (AT287_implies_long G) (AT287_implied_by_long G)

theorem AT288_implies_long (G : Type*) [Magma G] (h : AssociativeTheory288 G) : AssociativeTheory288_long G := by
  obtain ⟨eq4269, eq4343, eq4512⟩ := h
  have eq4273 := Equation4269_4343_4512_implies_Equation4273 G eq4269 eq4343 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4321, eq4343, eq4512⟩

theorem AT288_implied_by_long (G : Type*) [Magma G] : AssociativeTheory288_long G -> AssociativeTheory288 G :=
fun ⟨_, h4269, _, _, _, _, h4343, h4512⟩ => ⟨h4269, h4343, h4512⟩

theorem AT288_equiv (G : Type*) [Magma G] : AssociativeTheory288 G <-> AssociativeTheory288_long G :=
Iff.intro (AT288_implies_long G) (AT288_implied_by_long G)

theorem AT289_implies_long (G : Type*) [Magma G] (h : AssociativeTheory289 G) : AssociativeTheory289_long G := by
  obtain ⟨eq4268, eq4269, eq4343, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4275 := Equation4268_4343_4512_implies_Equation4275 G eq4268 eq4343 eq4512
  have eq4273 := Equation4269_4343_4512_implies_Equation4273 G eq4269 eq4343 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4276 := Equation4301_4512_implies_Equation4276 G eq4301 eq4512
  have eq4293 := Equation4301_4512_implies_Equation4293 G eq4301 eq4512
  have eq4321 := Equation4301_4512_implies_Equation4321 G eq4301 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4273, eq4275, eq4276, eq4277, eq4279, eq4283, eq4286, eq4291, eq4293, eq4296, eq4301, eq4305, eq4321, eq4343, eq4512⟩

theorem AT289_implied_by_long (G : Type*) [Magma G] : AssociativeTheory289_long G -> AssociativeTheory289 G :=
fun ⟨_, h4268, h4269, _, _, _, _, _, _, _, _, _, _, _, _, _, h4343, h4512⟩ => ⟨h4268, h4269, h4343, h4512⟩

theorem AT289_equiv (G : Type*) [Magma G] : AssociativeTheory289 G <-> AssociativeTheory289_long G :=
Iff.intro (AT289_implies_long G) (AT289_implied_by_long G)

theorem AT290_implies_long (G : Type*) [Magma G] (h : AssociativeTheory290 G) : AssociativeTheory290_long G := by
  obtain ⟨eq4276, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4343, eq4512⟩

theorem AT290_implied_by_long (G : Type*) [Magma G] : AssociativeTheory290_long G -> AssociativeTheory290 G :=
fun ⟨_, h4276, h4343, h4512⟩ => ⟨h4276, h4343, h4512⟩

theorem AT290_equiv (G : Type*) [Magma G] : AssociativeTheory290 G <-> AssociativeTheory290_long G :=
Iff.intro (AT290_implies_long G) (AT290_implied_by_long G)

theorem AT291_implies_long (G : Type*) [Magma G] (h : AssociativeTheory291 G) : AssociativeTheory291_long G := by
  obtain ⟨eq4283, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4343, eq4512⟩

theorem AT291_implied_by_long (G : Type*) [Magma G] : AssociativeTheory291_long G -> AssociativeTheory291 G :=
fun ⟨_, h4283, h4343, h4512⟩ => ⟨h4283, h4343, h4512⟩

theorem AT291_equiv (G : Type*) [Magma G] : AssociativeTheory291 G <-> AssociativeTheory291_long G :=
Iff.intro (AT291_implies_long G) (AT291_implied_by_long G)

theorem AT292_implies_long (G : Type*) [Magma G] (h : AssociativeTheory292 G) : AssociativeTheory292_long G := by
  obtain ⟨eq4276, eq4283, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4343, eq4512⟩

theorem AT292_implied_by_long (G : Type*) [Magma G] : AssociativeTheory292_long G -> AssociativeTheory292 G :=
fun ⟨_, h4276, h4283, h4343, h4512⟩ => ⟨h4276, h4283, h4343, h4512⟩

theorem AT292_equiv (G : Type*) [Magma G] : AssociativeTheory292 G <-> AssociativeTheory292_long G :=
Iff.intro (AT292_implies_long G) (AT292_implied_by_long G)

theorem AT293_implies_long (G : Type*) [Magma G] (h : AssociativeTheory293 G) : AssociativeTheory293_long G := by
  obtain ⟨eq4291, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4291, eq4343, eq4512⟩

theorem AT293_implied_by_long (G : Type*) [Magma G] : AssociativeTheory293_long G -> AssociativeTheory293 G :=
fun ⟨_, h4291, h4343, h4512⟩ => ⟨h4291, h4343, h4512⟩

theorem AT293_equiv (G : Type*) [Magma G] : AssociativeTheory293 G <-> AssociativeTheory293_long G :=
Iff.intro (AT293_implies_long G) (AT293_implied_by_long G)

theorem AT294_implies_long (G : Type*) [Magma G] (h : AssociativeTheory294 G) : AssociativeTheory294_long G := by
  obtain ⟨eq4276, eq4291, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4291, eq4343, eq4512⟩

theorem AT294_implied_by_long (G : Type*) [Magma G] : AssociativeTheory294_long G -> AssociativeTheory294 G :=
fun ⟨_, h4276, h4291, h4343, h4512⟩ => ⟨h4276, h4291, h4343, h4512⟩

theorem AT294_equiv (G : Type*) [Magma G] : AssociativeTheory294 G <-> AssociativeTheory294_long G :=
Iff.intro (AT294_implies_long G) (AT294_implied_by_long G)

theorem AT295_implies_long (G : Type*) [Magma G] (h : AssociativeTheory295 G) : AssociativeTheory295_long G := by
  obtain ⟨eq4283, eq4291, eq4343, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4343, eq4512⟩

theorem AT295_implied_by_long (G : Type*) [Magma G] : AssociativeTheory295_long G -> AssociativeTheory295 G :=
fun ⟨_, h4283, h4291, _, _, h4343, h4512⟩ => ⟨h4283, h4291, h4343, h4512⟩

theorem AT295_equiv (G : Type*) [Magma G] : AssociativeTheory295 G <-> AssociativeTheory295_long G :=
Iff.intro (AT295_implies_long G) (AT295_implied_by_long G)

theorem AT296_implies_long (G : Type*) [Magma G] (h : AssociativeTheory296 G) : AssociativeTheory296_long G := by
  obtain ⟨eq4276, eq4283, eq4291, eq4343, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4343, eq4512⟩

theorem AT296_implied_by_long (G : Type*) [Magma G] : AssociativeTheory296_long G -> AssociativeTheory296 G :=
fun ⟨_, h4276, h4283, h4291, _, _, h4343, h4512⟩ => ⟨h4276, h4283, h4291, h4343, h4512⟩

theorem AT296_equiv (G : Type*) [Magma G] : AssociativeTheory296 G <-> AssociativeTheory296_long G :=
Iff.intro (AT296_implies_long G) (AT296_implied_by_long G)

theorem AT297_implies_long (G : Type*) [Magma G] (h : AssociativeTheory297 G) : AssociativeTheory297_long G := by
  obtain ⟨eq4293, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4343, eq4512⟩

theorem AT297_implied_by_long (G : Type*) [Magma G] : AssociativeTheory297_long G -> AssociativeTheory297 G :=
fun ⟨_, h4293, h4343, h4512⟩ => ⟨h4293, h4343, h4512⟩

theorem AT297_equiv (G : Type*) [Magma G] : AssociativeTheory297 G <-> AssociativeTheory297_long G :=
Iff.intro (AT297_implies_long G) (AT297_implied_by_long G)

theorem AT298_implies_long (G : Type*) [Magma G] (h : AssociativeTheory298 G) : AssociativeTheory298_long G := by
  obtain ⟨eq4269, eq4293, eq4343, eq4512⟩ := h
  have eq4273 := Equation4269_4293_4512_implies_Equation4273 G eq4269 eq4293 eq4512
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4293, eq4321, eq4343, eq4512⟩

theorem AT298_implied_by_long (G : Type*) [Magma G] : AssociativeTheory298_long G -> AssociativeTheory298 G :=
fun ⟨_, h4269, _, _, _, h4293, _, h4343, h4512⟩ => ⟨h4269, h4293, h4343, h4512⟩

theorem AT298_equiv (G : Type*) [Magma G] : AssociativeTheory298 G <-> AssociativeTheory298_long G :=
Iff.intro (AT298_implies_long G) (AT298_implied_by_long G)

theorem AT299_implies_long (G : Type*) [Magma G] (h : AssociativeTheory299 G) : AssociativeTheory299_long G := by
  obtain ⟨eq4276, eq4293, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4343, eq4512⟩

theorem AT299_implied_by_long (G : Type*) [Magma G] : AssociativeTheory299_long G -> AssociativeTheory299 G :=
fun ⟨_, h4276, h4293, h4343, h4512⟩ => ⟨h4276, h4293, h4343, h4512⟩

theorem AT299_equiv (G : Type*) [Magma G] : AssociativeTheory299 G <-> AssociativeTheory299_long G :=
Iff.intro (AT299_implies_long G) (AT299_implied_by_long G)

theorem AT300_implies_long (G : Type*) [Magma G] (h : AssociativeTheory300 G) : AssociativeTheory300_long G := by
  obtain ⟨eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4321, eq4343, eq4512⟩

theorem AT300_implied_by_long (G : Type*) [Magma G] : AssociativeTheory300_long G -> AssociativeTheory300 G :=
fun ⟨_, h4321, h4343, h4512⟩ => ⟨h4321, h4343, h4512⟩

theorem AT300_equiv (G : Type*) [Magma G] : AssociativeTheory300 G <-> AssociativeTheory300_long G :=
Iff.intro (AT300_implies_long G) (AT300_implied_by_long G)

theorem AT301_implies_long (G : Type*) [Magma G] (h : AssociativeTheory301 G) : AssociativeTheory301_long G := by
  obtain ⟨eq307, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4321, eq4343, eq4512⟩

theorem AT301_implied_by_long (G : Type*) [Magma G] : AssociativeTheory301_long G -> AssociativeTheory301 G :=
fun ⟨_, h307, _, h4321, h4343, h4512⟩ => ⟨h307, h4321, h4343, h4512⟩

theorem AT301_equiv (G : Type*) [Magma G] : AssociativeTheory301 G <-> AssociativeTheory301_long G :=
Iff.intro (AT301_implies_long G) (AT301_implied_by_long G)

theorem AT302_implies_long (G : Type*) [Magma G] (h : AssociativeTheory302 G) : AssociativeTheory302_long G := by
  obtain ⟨eq4268, eq4321, eq4343, eq4512⟩ := h
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4321, eq4343, eq4512⟩

theorem AT302_implied_by_long (G : Type*) [Magma G] : AssociativeTheory302_long G -> AssociativeTheory302 G :=
fun ⟨_, h4268, _, _, _, _, h4321, h4343, h4512⟩ => ⟨h4268, h4321, h4343, h4512⟩

theorem AT302_equiv (G : Type*) [Magma G] : AssociativeTheory302 G <-> AssociativeTheory302_long G :=
Iff.intro (AT302_implies_long G) (AT302_implied_by_long G)

theorem AT303_implies_long (G : Type*) [Magma G] (h : AssociativeTheory303 G) : AssociativeTheory303_long G := by
  obtain ⟨eq4276, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4321, eq4343, eq4512⟩

theorem AT303_implied_by_long (G : Type*) [Magma G] : AssociativeTheory303_long G -> AssociativeTheory303 G :=
fun ⟨_, h4276, h4321, h4343, h4512⟩ => ⟨h4276, h4321, h4343, h4512⟩

theorem AT303_equiv (G : Type*) [Magma G] : AssociativeTheory303 G <-> AssociativeTheory303_long G :=
Iff.intro (AT303_implies_long G) (AT303_implied_by_long G)

theorem AT304_implies_long (G : Type*) [Magma G] (h : AssociativeTheory304 G) : AssociativeTheory304_long G := by
  obtain ⟨eq4293, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4321, eq4343, eq4512⟩

theorem AT304_implied_by_long (G : Type*) [Magma G] : AssociativeTheory304_long G -> AssociativeTheory304 G :=
fun ⟨_, h4293, h4321, h4343, h4512⟩ => ⟨h4293, h4321, h4343, h4512⟩

theorem AT304_equiv (G : Type*) [Magma G] : AssociativeTheory304 G <-> AssociativeTheory304_long G :=
Iff.intro (AT304_implies_long G) (AT304_implied_by_long G)

theorem AT305_implies_long (G : Type*) [Magma G] (h : AssociativeTheory305 G) : AssociativeTheory305_long G := by
  obtain ⟨eq4276, eq4293, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4321, eq4343, eq4512⟩

theorem AT305_implied_by_long (G : Type*) [Magma G] : AssociativeTheory305_long G -> AssociativeTheory305 G :=
fun ⟨_, h4276, h4293, h4321, h4343, h4512⟩ => ⟨h4276, h4293, h4321, h4343, h4512⟩

theorem AT305_equiv (G : Type*) [Magma G] : AssociativeTheory305 G <-> AssociativeTheory305_long G :=
Iff.intro (AT305_implies_long G) (AT305_implied_by_long G)

theorem AT306_implies_long (G : Type*) [Magma G] (h : AssociativeTheory306 G) : AssociativeTheory306_long G := by
  obtain ⟨eq4358, eq4512⟩ := h
  have eq1 := Equation4358_4512_implies_Equation1 G eq4358 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4283, eq4358, eq4512⟩

theorem AT306_implied_by_long (G : Type*) [Magma G] : AssociativeTheory306_long G -> AssociativeTheory306 G :=
fun ⟨_, _, h4358, h4512⟩ => ⟨h4358, h4512⟩

theorem AT306_equiv (G : Type*) [Magma G] : AssociativeTheory306 G <-> AssociativeTheory306_long G :=
Iff.intro (AT306_implies_long G) (AT306_implied_by_long G)

theorem AT307_implies_long (G : Type*) [Magma G] (h : AssociativeTheory307 G) : AssociativeTheory307_long G := by
  obtain ⟨eq3, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  have eq307 := Equation3_4512_implies_Equation307 G eq3 eq4512
  have eq323 := Equation3_4512_implies_Equation323 G eq3 eq4512
  have eq326 := Equation3_4512_implies_Equation326 G eq3 eq4512
  have eq411 := Equation3_4512_implies_Equation411 G eq3 eq4512
  have eq3253 := Equation3_4512_implies_Equation3253 G eq3 eq4512
  have eq3306 := Equation3_4512_implies_Equation3306 G eq3 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3_4512_implies_Equation3316 G eq3 eq4512
  have eq3319 := Equation3_4512_implies_Equation3319 G eq3 eq4512
  have eq4284 := Equation3_4512_implies_Equation4284 G eq3 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq325 := Equation326_4314_4512_implies_Equation325 G eq326 eq4314 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  exact ⟨eq1, eq3, eq8, eq47, eq307, eq323, eq325, eq326, eq411, eq3253, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem AT307_implied_by_long (G : Type*) [Magma G] : AssociativeTheory307_long G -> AssociativeTheory307 G :=
fun ⟨_, h3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h3, h4358, h4512⟩

theorem AT307_equiv (G : Type*) [Magma G] : AssociativeTheory307 G <-> AssociativeTheory307_long G :=
Iff.intro (AT307_implies_long G) (AT307_implied_by_long G)

theorem AT308_implies_long (G : Type*) [Magma G] (h : AssociativeTheory308 G) : AssociativeTheory308_long G := by
  obtain ⟨eq8, eq4358, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4358, eq4512⟩

theorem AT308_implied_by_long (G : Type*) [Magma G] : AssociativeTheory308_long G -> AssociativeTheory308 G :=
fun ⟨_, h8, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h8, h4358, h4512⟩

theorem AT308_equiv (G : Type*) [Magma G] : AssociativeTheory308 G <-> AssociativeTheory308_long G :=
Iff.intro (AT308_implies_long G) (AT308_implied_by_long G)

theorem AT309_implies_long (G : Type*) [Magma G] (h : AssociativeTheory309 G) : AssociativeTheory309_long G := by
  obtain ⟨eq40, eq4358, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4273 := Equation4275_4283_4512_implies_Equation4273 G eq4275 eq4283 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4512⟩

theorem AT309_implied_by_long (G : Type*) [Magma G] : AssociativeTheory309_long G -> AssociativeTheory309 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h40, h4358, h4512⟩

theorem AT309_equiv (G : Type*) [Magma G] : AssociativeTheory309 G <-> AssociativeTheory309_long G :=
Iff.intro (AT309_implies_long G) (AT309_implied_by_long G)

theorem AT310_implies_long (G : Type*) [Magma G] (h : AssociativeTheory310 G) : AssociativeTheory310_long G := by
  obtain ⟨eq47, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq47, eq4283, eq4358, eq4512⟩

theorem AT310_implied_by_long (G : Type*) [Magma G] : AssociativeTheory310_long G -> AssociativeTheory310 G :=
fun ⟨_, h47, _, h4358, h4512⟩ => ⟨h47, h4358, h4512⟩

theorem AT310_equiv (G : Type*) [Magma G] : AssociativeTheory310 G <-> AssociativeTheory310_long G :=
Iff.intro (AT310_implies_long G) (AT310_implied_by_long G)

theorem AT311_implies_long (G : Type*) [Magma G] (h : AssociativeTheory311 G) : AssociativeTheory311_long G := by
  obtain ⟨eq307, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4358, eq4512⟩

theorem AT311_implied_by_long (G : Type*) [Magma G] : AssociativeTheory311_long G -> AssociativeTheory311 G :=
fun ⟨_, h307, _, _, h4358, h4512⟩ => ⟨h307, h4358, h4512⟩

theorem AT311_equiv (G : Type*) [Magma G] : AssociativeTheory311 G <-> AssociativeTheory311_long G :=
Iff.intro (AT311_implies_long G) (AT311_implied_by_long G)

theorem AT312_implies_long (G : Type*) [Magma G] (h : AssociativeTheory312 G) : AssociativeTheory312_long G := by
  obtain ⟨eq40, eq307, eq4358, eq4512⟩ := h
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq4273 := Equation4275_4283_4512_implies_Equation4273 G eq4275 eq4283 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq309 := Equation3258_4320_4512_implies_Equation309 G eq3258 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq3265 := Equation308_309_4512_implies_Equation3265 G eq308 eq309 eq4512
  have eq3260 := Equation308_309_4512_implies_Equation3260 G eq308 eq309 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4512⟩

theorem AT312_implied_by_long (G : Type*) [Magma G] : AssociativeTheory312_long G -> AssociativeTheory312 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h40, h307, h4358, h4512⟩

theorem AT312_equiv (G : Type*) [Magma G] : AssociativeTheory312 G <-> AssociativeTheory312_long G :=
Iff.intro (AT312_implies_long G) (AT312_implied_by_long G)

theorem AT313_implies_long (G : Type*) [Magma G] (h : AssociativeTheory313 G) : AssociativeTheory313_long G := by
  obtain ⟨eq308, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation308_4512_implies_Equation307 G eq308 eq4512
  have eq3253 := Equation308_4512_implies_Equation3253 G eq308 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq3259 := Equation3256_4283_4512_implies_Equation3259 G eq3256 eq4283 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq309 := Equation307_4269_4512_implies_Equation309 G eq307 eq4269 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq3265 := Equation308_309_4512_implies_Equation3265 G eq308 eq309 eq4512
  have eq3260 := Equation308_309_4512_implies_Equation3260 G eq308 eq309 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq310 := Equation308_4284_4512_implies_Equation310 G eq308 eq4284 eq4512
  exact ⟨eq1, eq307, eq308, eq309, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4358, eq4512⟩

theorem AT313_implied_by_long (G : Type*) [Magma G] : AssociativeTheory313_long G -> AssociativeTheory313 G :=
fun ⟨_, _, h308, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h308, h4358, h4512⟩

theorem AT313_equiv (G : Type*) [Magma G] : AssociativeTheory313 G <-> AssociativeTheory313_long G :=
Iff.intro (AT313_implies_long G) (AT313_implied_by_long G)

theorem AT314_implies_long (G : Type*) [Magma G] (h : AssociativeTheory314 G) : AssociativeTheory314_long G := by
  obtain ⟨eq323, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq3319 := Equation3308_4512_implies_Equation3319 G eq3308 eq4512
  have eq325 := Equation307_3315_4512_implies_Equation325 G eq307 eq3315 eq4512
  have eq326 := Equation307_3319_4512_implies_Equation326 G eq307 eq3319 eq4512
  have eq3309 := Equation323_326_4512_implies_Equation3309 G eq323 eq326 eq4512
  have eq3316 := Equation325_4512_implies_Equation3316 G eq325 eq4512
  have eq4314 := Equation325_4512_implies_Equation4314 G eq325 eq4512
  have eq4284 := Equation4283_4314_4512_implies_Equation4284 G eq4283 eq4314 eq4512
  exact ⟨eq1, eq307, eq323, eq325, eq326, eq3253, eq3306, eq3308, eq3309, eq3315, eq3316, eq3319, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem AT314_implied_by_long (G : Type*) [Magma G] : AssociativeTheory314_long G -> AssociativeTheory314 G :=
fun ⟨_, _, h323, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h323, h4358, h4512⟩

theorem AT314_equiv (G : Type*) [Magma G] : AssociativeTheory314 G <-> AssociativeTheory314_long G :=
Iff.intro (AT314_implies_long G) (AT314_implied_by_long G)

theorem AT315_implies_long (G : Type*) [Magma G] (h : AssociativeTheory315 G) : AssociativeTheory315_long G := by
  obtain ⟨eq326, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4283, eq4358, eq4512⟩

theorem AT315_implied_by_long (G : Type*) [Magma G] : AssociativeTheory315_long G -> AssociativeTheory315 G :=
fun ⟨_, _, h326, _, _, _, h4358, h4512⟩ => ⟨h326, h4358, h4512⟩

theorem AT315_equiv (G : Type*) [Magma G] : AssociativeTheory315 G <-> AssociativeTheory315_long G :=
Iff.intro (AT315_implies_long G) (AT315_implied_by_long G)

theorem AT316_implies_long (G : Type*) [Magma G] (h : AssociativeTheory316 G) : AssociativeTheory316_long G := by
  obtain ⟨eq411, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq411, eq4283, eq4358, eq4512⟩

theorem AT316_implied_by_long (G : Type*) [Magma G] : AssociativeTheory316_long G -> AssociativeTheory316 G :=
fun ⟨_, h411, _, h4358, h4512⟩ => ⟨h411, h4358, h4512⟩

theorem AT316_equiv (G : Type*) [Magma G] : AssociativeTheory316 G <-> AssociativeTheory316_long G :=
Iff.intro (AT316_implies_long G) (AT316_implied_by_long G)

theorem AT317_implies_long (G : Type*) [Magma G] (h : AssociativeTheory317 G) : AssociativeTheory317_long G := by
  obtain ⟨eq3253, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4358, eq4512⟩

theorem AT317_implied_by_long (G : Type*) [Magma G] : AssociativeTheory317_long G -> AssociativeTheory317 G :=
fun ⟨_, h3253, _, h4358, h4512⟩ => ⟨h3253, h4358, h4512⟩

theorem AT317_equiv (G : Type*) [Magma G] : AssociativeTheory317 G <-> AssociativeTheory317_long G :=
Iff.intro (AT317_implies_long G) (AT317_implied_by_long G)

theorem AT318_implies_long (G : Type*) [Magma G] (h : AssociativeTheory318 G) : AssociativeTheory318_long G := by
  obtain ⟨eq3256, eq4358, eq4512⟩ := h
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3259 := Equation3256_4283_4512_implies_Equation3259 G eq3256 eq4283 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq4270, eq4283, eq4358, eq4512⟩

theorem AT318_implied_by_long (G : Type*) [Magma G] : AssociativeTheory318_long G -> AssociativeTheory318 G :=
fun ⟨_, _, h3256, _, _, _, _, h4358, h4512⟩ => ⟨h3256, h4358, h4512⟩

theorem AT318_equiv (G : Type*) [Magma G] : AssociativeTheory318 G <-> AssociativeTheory318_long G :=
Iff.intro (AT318_implies_long G) (AT318_implied_by_long G)

theorem AT319_implies_long (G : Type*) [Magma G] (h : AssociativeTheory319 G) : AssociativeTheory319_long G := by
  obtain ⟨eq3267, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq309 := Equation307_4269_4512_implies_Equation309 G eq307 eq4269 eq4512
  exact ⟨eq1, eq307, eq308, eq309, eq310, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4358, eq4512⟩

theorem AT319_implied_by_long (G : Type*) [Magma G] : AssociativeTheory319_long G -> AssociativeTheory319 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h3267, h4358, h4512⟩

theorem AT319_equiv (G : Type*) [Magma G] : AssociativeTheory319 G <-> AssociativeTheory319_long G :=
Iff.intro (AT319_implies_long G) (AT319_implied_by_long G)

theorem AT320_implies_long (G : Type*) [Magma G] (h : AssociativeTheory320 G) : AssociativeTheory320_long G := by
  obtain ⟨eq40, eq3267, eq4358, eq4512⟩ := h
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4273 := Equation4275_4283_4512_implies_Equation4273 G eq4275 eq4283 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq315 := Equation3277_4512_implies_Equation315 G eq3277 eq4512
  have eq3274 := Equation3277_4512_implies_Equation3274 G eq3277 eq4512
  have eq3292 := Equation3277_4512_implies_Equation3292 G eq3277 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  have eq4276 := Equation3277_4512_implies_Equation4276 G eq3277 eq4512
  have eq4280 := Equation3277_4512_implies_Equation4280 G eq3277 eq4512
  have eq4299 := Equation3277_4512_implies_Equation4299 G eq3277 eq4512
  have eq4304 := Equation3277_4512_implies_Equation4304 G eq3277 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq309 := Equation307_4269_4512_implies_Equation309 G eq307 eq4269 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4512⟩

theorem AT320_implied_by_long (G : Type*) [Magma G] : AssociativeTheory320_long G -> AssociativeTheory320 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h40, h3267, h4358, h4512⟩

theorem AT320_equiv (G : Type*) [Magma G] : AssociativeTheory320 G <-> AssociativeTheory320_long G :=
Iff.intro (AT320_implies_long G) (AT320_implied_by_long G)

theorem AT321_implies_long (G : Type*) [Magma G] (h : AssociativeTheory321 G) : AssociativeTheory321_long G := by
  obtain ⟨eq3306, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq3319 := Equation3308_4512_implies_Equation3319 G eq3308 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4358, eq4512⟩

theorem AT321_implied_by_long (G : Type*) [Magma G] : AssociativeTheory321_long G -> AssociativeTheory321 G :=
fun ⟨_, _, h3306, _, _, _, _, h4358, h4512⟩ => ⟨h3306, h4358, h4512⟩

theorem AT321_equiv (G : Type*) [Magma G] : AssociativeTheory321 G <-> AssociativeTheory321_long G :=
Iff.intro (AT321_implies_long G) (AT321_implied_by_long G)

theorem AT322_implies_long (G : Type*) [Magma G] (h : AssociativeTheory322 G) : AssociativeTheory322_long G := by
  obtain ⟨eq3319, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact ⟨eq1, eq3253, eq3319, eq4283, eq4358, eq4512⟩

theorem AT322_implied_by_long (G : Type*) [Magma G] : AssociativeTheory322_long G -> AssociativeTheory322 G :=
fun ⟨_, _, h3319, _, h4358, h4512⟩ => ⟨h3319, h4358, h4512⟩

theorem AT322_equiv (G : Type*) [Magma G] : AssociativeTheory322 G <-> AssociativeTheory322_long G :=
Iff.intro (AT322_implies_long G) (AT322_implied_by_long G)

theorem AT323_implies_long (G : Type*) [Magma G] (h : AssociativeTheory323 G) : AssociativeTheory323_long G := by
  obtain ⟨eq4268, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4283, eq4286, eq4358, eq4512⟩

theorem AT323_implied_by_long (G : Type*) [Magma G] : AssociativeTheory323_long G -> AssociativeTheory323 G :=
fun ⟨_, h4268, _, _, _, h4358, h4512⟩ => ⟨h4268, h4358, h4512⟩

theorem AT323_equiv (G : Type*) [Magma G] : AssociativeTheory323 G <-> AssociativeTheory323_long G :=
Iff.intro (AT323_implies_long G) (AT323_implied_by_long G)

theorem AT324_implies_long (G : Type*) [Magma G] (h : AssociativeTheory324 G) : AssociativeTheory324_long G := by
  obtain ⟨eq4270, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4270, eq4283, eq4358, eq4512⟩

theorem AT324_implied_by_long (G : Type*) [Magma G] : AssociativeTheory324_long G -> AssociativeTheory324 G :=
fun ⟨_, h4270, _, h4358, h4512⟩ => ⟨h4270, h4358, h4512⟩

theorem AT324_equiv (G : Type*) [Magma G] : AssociativeTheory324 G <-> AssociativeTheory324_long G :=
Iff.intro (AT324_implies_long G) (AT324_implied_by_long G)

theorem AT325_implies_long (G : Type*) [Magma G] (h : AssociativeTheory325 G) : AssociativeTheory325_long G := by
  obtain ⟨eq4268, eq4270, eq4358, eq4512⟩ := h
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4358, eq4512⟩

theorem AT325_implied_by_long (G : Type*) [Magma G] : AssociativeTheory325_long G -> AssociativeTheory325 G :=
fun ⟨_, h4268, _, h4270, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4268, h4270, h4358, h4512⟩

theorem AT325_equiv (G : Type*) [Magma G] : AssociativeTheory325 G <-> AssociativeTheory325_long G :=
Iff.intro (AT325_implies_long G) (AT325_implied_by_long G)

theorem AT326_implies_long (G : Type*) [Magma G] (h : AssociativeTheory326 G) : AssociativeTheory326_long G := by
  obtain ⟨eq4272, eq4358, eq4512⟩ := h
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4343, eq4358, eq4512⟩

theorem AT326_implied_by_long (G : Type*) [Magma G] : AssociativeTheory326_long G -> AssociativeTheory326 G :=
fun ⟨_, _, h4272, _, _, _, _, h4358, h4512⟩ => ⟨h4272, h4358, h4512⟩

theorem AT326_equiv (G : Type*) [Magma G] : AssociativeTheory326 G <-> AssociativeTheory326_long G :=
Iff.intro (AT326_implies_long G) (AT326_implied_by_long G)

theorem AT327_implies_long (G : Type*) [Magma G] (h : AssociativeTheory327 G) : AssociativeTheory327_long G := by
  obtain ⟨eq4268, eq4272, eq4358, eq4512⟩ := h
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4275 := Equation4299_4512_implies_Equation4275 G eq4299 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  have eq4290 := Equation4299_4512_implies_Equation4290 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4297 := Equation4299_4512_implies_Equation4297 G eq4299 eq4512
  have eq4304 := Equation4299_4512_implies_Equation4304 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4512⟩

theorem AT327_implied_by_long (G : Type*) [Magma G] : AssociativeTheory327_long G -> AssociativeTheory327 G :=
fun ⟨_, h4268, _, _, h4272, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4268, h4272, h4358, h4512⟩

theorem AT327_equiv (G : Type*) [Magma G] : AssociativeTheory327 G <-> AssociativeTheory327_long G :=
Iff.intro (AT327_implies_long G) (AT327_implied_by_long G)

theorem AT328_implies_long (G : Type*) [Magma G] (h : AssociativeTheory328 G) : AssociativeTheory328_long G := by
  obtain ⟨eq4273, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4275 := Equation4273_4283_4512_implies_Equation4275 G eq4273 eq4283 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4273, eq4275, eq4283, eq4305, eq4358, eq4512⟩

theorem AT328_implied_by_long (G : Type*) [Magma G] : AssociativeTheory328_long G -> AssociativeTheory328 G :=
fun ⟨_, h4273, _, _, _, h4358, h4512⟩ => ⟨h4273, h4358, h4512⟩

theorem AT328_equiv (G : Type*) [Magma G] : AssociativeTheory328 G <-> AssociativeTheory328_long G :=
Iff.intro (AT328_implies_long G) (AT328_implied_by_long G)

theorem AT329_implies_long (G : Type*) [Magma G] (h : AssociativeTheory329 G) : AssociativeTheory329_long G := by
  obtain ⟨eq4268, eq4273, eq4358, eq4512⟩ := h
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4275 := Equation4273_4283_4512_implies_Equation4275 G eq4273 eq4283 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4276 := Equation4301_4512_implies_Equation4276 G eq4301 eq4512
  have eq4277 := Equation4301_4512_implies_Equation4277 G eq4301 eq4512
  have eq4279 := Equation4301_4512_implies_Equation4279 G eq4301 eq4512
  have eq4286 := Equation4301_4512_implies_Equation4286 G eq4301 eq4512
  have eq4291 := Equation4301_4512_implies_Equation4291 G eq4301 eq4512
  have eq4293 := Equation4301_4512_implies_Equation4293 G eq4301 eq4512
  have eq4296 := Equation4301_4512_implies_Equation4296 G eq4301 eq4512
  have eq4305 := Equation4301_4512_implies_Equation4305 G eq4301 eq4512
  have eq4321 := Equation4301_4512_implies_Equation4321 G eq4301 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4273, eq4275, eq4276, eq4277, eq4279, eq4283, eq4286, eq4291, eq4293, eq4296, eq4301, eq4305, eq4321, eq4358, eq4512⟩

theorem AT329_implied_by_long (G : Type*) [Magma G] : AssociativeTheory329_long G -> AssociativeTheory329 G :=
fun ⟨_, h4268, _, h4273, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4268, h4273, h4358, h4512⟩

theorem AT329_equiv (G : Type*) [Magma G] : AssociativeTheory329 G <-> AssociativeTheory329_long G :=
Iff.intro (AT329_implies_long G) (AT329_implied_by_long G)

theorem AT330_implies_long (G : Type*) [Magma G] (h : AssociativeTheory330 G) : AssociativeTheory330_long G := by
  obtain ⟨eq4270, eq4273, eq4358, eq4512⟩ := h
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4275 := Equation4273_4283_4512_implies_Equation4275 G eq4273 eq4283 eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4512⟩

theorem AT330_implied_by_long (G : Type*) [Magma G] : AssociativeTheory330_long G -> AssociativeTheory330 G :=
fun ⟨_, h4270, h4273, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4270, h4273, h4358, h4512⟩

theorem AT330_equiv (G : Type*) [Magma G] : AssociativeTheory330 G <-> AssociativeTheory330_long G :=
Iff.intro (AT330_implies_long G) (AT330_implied_by_long G)

theorem AT331_implies_long (G : Type*) [Magma G] (h : AssociativeTheory331 G) : AssociativeTheory331_long G := by
  obtain ⟨eq4276, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4358, eq4512⟩

theorem AT331_implied_by_long (G : Type*) [Magma G] : AssociativeTheory331_long G -> AssociativeTheory331 G :=
fun ⟨_, h4276, _, h4358, h4512⟩ => ⟨h4276, h4358, h4512⟩

theorem AT331_equiv (G : Type*) [Magma G] : AssociativeTheory331 G <-> AssociativeTheory331_long G :=
Iff.intro (AT331_implies_long G) (AT331_implied_by_long G)

theorem AT332_implies_long (G : Type*) [Magma G] (h : AssociativeTheory332 G) : AssociativeTheory332_long G := by
  obtain ⟨eq4284, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem AT332_implied_by_long (G : Type*) [Magma G] : AssociativeTheory332_long G -> AssociativeTheory332 G :=
fun ⟨_, _, h4284, _, h4358, h4512⟩ => ⟨h4284, h4358, h4512⟩

theorem AT332_equiv (G : Type*) [Magma G] : AssociativeTheory332 G <-> AssociativeTheory332_long G :=
Iff.intro (AT332_implies_long G) (AT332_implied_by_long G)

theorem AT333_implies_long (G : Type*) [Magma G] (h : AssociativeTheory333 G) : AssociativeTheory333_long G := by
  obtain ⟨eq307, eq4284, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem AT333_implied_by_long (G : Type*) [Magma G] : AssociativeTheory333_long G -> AssociativeTheory333 G :=
fun ⟨_, h307, _, _, h4284, _, h4358, h4512⟩ => ⟨h307, h4284, h4358, h4512⟩

theorem AT333_equiv (G : Type*) [Magma G] : AssociativeTheory333 G <-> AssociativeTheory333_long G :=
Iff.intro (AT333_implies_long G) (AT333_implied_by_long G)

theorem AT334_implies_long (G : Type*) [Magma G] (h : AssociativeTheory334 G) : AssociativeTheory334_long G := by
  obtain ⟨eq4276, eq4284, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem AT334_implied_by_long (G : Type*) [Magma G] : AssociativeTheory334_long G -> AssociativeTheory334 G :=
fun ⟨_, h4276, _, h4284, _, h4358, h4512⟩ => ⟨h4276, h4284, h4358, h4512⟩

theorem AT334_equiv (G : Type*) [Magma G] : AssociativeTheory334 G <-> AssociativeTheory334_long G :=
Iff.intro (AT334_implies_long G) (AT334_implied_by_long G)

theorem AT335_implies_long (G : Type*) [Magma G] (h : AssociativeTheory335 G) : AssociativeTheory335_long G := by
  obtain ⟨eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem AT335_implied_by_long (G : Type*) [Magma G] : AssociativeTheory335_long G -> AssociativeTheory335 G :=
fun ⟨_, _, h4290, _, h4358, h4512⟩ => ⟨h4290, h4358, h4512⟩

theorem AT335_equiv (G : Type*) [Magma G] : AssociativeTheory335 G <-> AssociativeTheory335_long G :=
Iff.intro (AT335_implies_long G) (AT335_implied_by_long G)

theorem AT336_implies_long (G : Type*) [Magma G] (h : AssociativeTheory336 G) : AssociativeTheory336_long G := by
  obtain ⟨eq307, eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem AT336_implied_by_long (G : Type*) [Magma G] : AssociativeTheory336_long G -> AssociativeTheory336 G :=
fun ⟨_, h307, _, _, h4290, _, h4358, h4512⟩ => ⟨h307, h4290, h4358, h4512⟩

theorem AT336_equiv (G : Type*) [Magma G] : AssociativeTheory336 G <-> AssociativeTheory336_long G :=
Iff.intro (AT336_implies_long G) (AT336_implied_by_long G)

theorem AT337_implies_long (G : Type*) [Magma G] (h : AssociativeTheory337 G) : AssociativeTheory337_long G := by
  obtain ⟨eq3253, eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem AT337_implied_by_long (G : Type*) [Magma G] : AssociativeTheory337_long G -> AssociativeTheory337 G :=
fun ⟨_, h3253, _, h4290, _, h4358, h4512⟩ => ⟨h3253, h4290, h4358, h4512⟩

theorem AT337_equiv (G : Type*) [Magma G] : AssociativeTheory337 G <-> AssociativeTheory337_long G :=
Iff.intro (AT337_implies_long G) (AT337_implied_by_long G)

theorem AT338_implies_long (G : Type*) [Magma G] (h : AssociativeTheory338 G) : AssociativeTheory338_long G := by
  obtain ⟨eq4276, eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem AT338_implied_by_long (G : Type*) [Magma G] : AssociativeTheory338_long G -> AssociativeTheory338 G :=
fun ⟨_, h4276, _, h4290, _, h4358, h4512⟩ => ⟨h4276, h4290, h4358, h4512⟩

theorem AT338_equiv (G : Type*) [Magma G] : AssociativeTheory338 G <-> AssociativeTheory338_long G :=
Iff.intro (AT338_implies_long G) (AT338_implied_by_long G)

theorem AT339_implies_long (G : Type*) [Magma G] (h : AssociativeTheory339 G) : AssociativeTheory339_long G := by
  obtain ⟨eq4284, eq4290, eq4358, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4512⟩

theorem AT339_implied_by_long (G : Type*) [Magma G] : AssociativeTheory339_long G -> AssociativeTheory339 G :=
fun ⟨_, _, h4284, h4290, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4284, h4290, h4358, h4512⟩

theorem AT339_equiv (G : Type*) [Magma G] : AssociativeTheory339 G <-> AssociativeTheory339_long G :=
Iff.intro (AT339_implies_long G) (AT339_implied_by_long G)

theorem AT340_implies_long (G : Type*) [Magma G] (h : AssociativeTheory340 G) : AssociativeTheory340_long G := by
  obtain ⟨eq307, eq4284, eq4290, eq4358, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4512⟩

theorem AT340_implied_by_long (G : Type*) [Magma G] : AssociativeTheory340_long G -> AssociativeTheory340 G :=
fun ⟨_, h307, _, _, h4284, h4290, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h307, h4284, h4290, h4358, h4512⟩

theorem AT340_equiv (G : Type*) [Magma G] : AssociativeTheory340 G <-> AssociativeTheory340_long G :=
Iff.intro (AT340_implies_long G) (AT340_implied_by_long G)

theorem AT341_implies_long (G : Type*) [Magma G] (h : AssociativeTheory341 G) : AssociativeTheory341_long G := by
  obtain ⟨eq4276, eq4284, eq4290, eq4358, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4512⟩

theorem AT341_implied_by_long (G : Type*) [Magma G] : AssociativeTheory341_long G -> AssociativeTheory341 G :=
fun ⟨_, h4276, _, h4284, h4290, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4276, h4284, h4290, h4358, h4512⟩

theorem AT341_equiv (G : Type*) [Magma G] : AssociativeTheory341 G <-> AssociativeTheory341_long G :=
Iff.intro (AT341_implies_long G) (AT341_implied_by_long G)

theorem AT342_implies_long (G : Type*) [Magma G] (h : AssociativeTheory342 G) : AssociativeTheory342_long G := by
  obtain ⟨eq4291, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem AT342_implied_by_long (G : Type*) [Magma G] : AssociativeTheory342_long G -> AssociativeTheory342 G :=
fun ⟨_, _, h4291, _, _, h4358, h4512⟩ => ⟨h4291, h4358, h4512⟩

theorem AT342_equiv (G : Type*) [Magma G] : AssociativeTheory342 G <-> AssociativeTheory342_long G :=
Iff.intro (AT342_implies_long G) (AT342_implied_by_long G)

theorem AT343_implies_long (G : Type*) [Magma G] (h : AssociativeTheory343 G) : AssociativeTheory343_long G := by
  obtain ⟨eq307, eq4291, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem AT343_implied_by_long (G : Type*) [Magma G] : AssociativeTheory343_long G -> AssociativeTheory343 G :=
fun ⟨_, h307, _, _, h4291, _, _, h4358, h4512⟩ => ⟨h307, h4291, h4358, h4512⟩

theorem AT343_equiv (G : Type*) [Magma G] : AssociativeTheory343 G <-> AssociativeTheory343_long G :=
Iff.intro (AT343_implies_long G) (AT343_implied_by_long G)

theorem AT344_implies_long (G : Type*) [Magma G] (h : AssociativeTheory344 G) : AssociativeTheory344_long G := by
  obtain ⟨eq4270, eq4291, eq4358, eq4512⟩ := h
  have eq4272 := Equation4270_4291_4512_implies_Equation4272 G eq4270 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4291, eq4293, eq4321, eq4343, eq4358, eq4512⟩

theorem AT344_implied_by_long (G : Type*) [Magma G] : AssociativeTheory344_long G -> AssociativeTheory344 G :=
fun ⟨_, h4270, _, _, _, _, h4291, _, _, _, h4358, h4512⟩ => ⟨h4270, h4291, h4358, h4512⟩

theorem AT344_equiv (G : Type*) [Magma G] : AssociativeTheory344 G <-> AssociativeTheory344_long G :=
Iff.intro (AT344_implies_long G) (AT344_implied_by_long G)

theorem AT345_implies_long (G : Type*) [Magma G] (h : AssociativeTheory345 G) : AssociativeTheory345_long G := by
  obtain ⟨eq4276, eq4291, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem AT345_implied_by_long (G : Type*) [Magma G] : AssociativeTheory345_long G -> AssociativeTheory345 G :=
fun ⟨_, h4276, _, h4291, _, _, h4358, h4512⟩ => ⟨h4276, h4291, h4358, h4512⟩

theorem AT345_equiv (G : Type*) [Magma G] : AssociativeTheory345 G <-> AssociativeTheory345_long G :=
Iff.intro (AT345_implies_long G) (AT345_implied_by_long G)

theorem AT346_implies_long (G : Type*) [Magma G] (h : AssociativeTheory346 G) : AssociativeTheory346_long G := by
  obtain ⟨eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4283, eq4343, eq4358, eq4512⟩

theorem AT346_implied_by_long (G : Type*) [Magma G] : AssociativeTheory346_long G -> AssociativeTheory346 G :=
fun ⟨_, _, h4343, h4358, h4512⟩ => ⟨h4343, h4358, h4512⟩

theorem AT346_equiv (G : Type*) [Magma G] : AssociativeTheory346 G <-> AssociativeTheory346_long G :=
Iff.intro (AT346_implies_long G) (AT346_implied_by_long G)

theorem AT347_implies_long (G : Type*) [Magma G] (h : AssociativeTheory347 G) : AssociativeTheory347_long G := by
  obtain ⟨eq4268, eq4343, eq4358, eq4512⟩ := h
  have eq4275 := Equation4268_4343_4512_implies_Equation4275 G eq4268 eq4343 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4273 := Equation4275_4283_4512_implies_Equation4273 G eq4275 eq4283 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq4321 := Equation4301_4512_implies_Equation4321 G eq4301 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4273, eq4275, eq4276, eq4277, eq4279, eq4283, eq4286, eq4291, eq4293, eq4296, eq4301, eq4305, eq4321, eq4343, eq4358, eq4512⟩

theorem AT347_implied_by_long (G : Type*) [Magma G] : AssociativeTheory347_long G -> AssociativeTheory347 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4343, h4358, h4512⟩ => ⟨h4268, h4343, h4358, h4512⟩

theorem AT347_equiv (G : Type*) [Magma G] : AssociativeTheory347 G <-> AssociativeTheory347_long G :=
Iff.intro (AT347_implies_long G) (AT347_implied_by_long G)

theorem AT348_implies_long (G : Type*) [Magma G] (h : AssociativeTheory348 G) : AssociativeTheory348_long G := by
  obtain ⟨eq4276, eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4343, eq4358, eq4512⟩

theorem AT348_implied_by_long (G : Type*) [Magma G] : AssociativeTheory348_long G -> AssociativeTheory348 G :=
fun ⟨_, h4276, _, h4343, h4358, h4512⟩ => ⟨h4276, h4343, h4358, h4512⟩

theorem AT348_equiv (G : Type*) [Magma G] : AssociativeTheory348 G <-> AssociativeTheory348_long G :=
Iff.intro (AT348_implies_long G) (AT348_implied_by_long G)

theorem AT349_implies_long (G : Type*) [Magma G] (h : AssociativeTheory349 G) : AssociativeTheory349_long G := by
  obtain ⟨eq4291, eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4343, eq4358, eq4512⟩

theorem AT349_implied_by_long (G : Type*) [Magma G] : AssociativeTheory349_long G -> AssociativeTheory349 G :=
fun ⟨_, _, h4291, _, _, h4343, h4358, h4512⟩ => ⟨h4291, h4343, h4358, h4512⟩

theorem AT349_equiv (G : Type*) [Magma G] : AssociativeTheory349 G <-> AssociativeTheory349_long G :=
Iff.intro (AT349_implies_long G) (AT349_implied_by_long G)

theorem AT350_implies_long (G : Type*) [Magma G] (h : AssociativeTheory350 G) : AssociativeTheory350_long G := by
  obtain ⟨eq4276, eq4291, eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4343, eq4358, eq4512⟩

theorem AT350_implied_by_long (G : Type*) [Magma G] : AssociativeTheory350_long G -> AssociativeTheory350 G :=
fun ⟨_, h4276, _, h4291, _, _, h4343, h4358, h4512⟩ => ⟨h4276, h4291, h4343, h4358, h4512⟩

theorem AT350_equiv (G : Type*) [Magma G] : AssociativeTheory350 G <-> AssociativeTheory350_long G :=
Iff.intro (AT350_implies_long G) (AT350_implied_by_long G)

theorem AT351_implies_long (G : Type*) [Magma G] (h : AssociativeTheory351 G) : AssociativeTheory351_long G := by
  obtain ⟨eq4362, eq4512⟩ := h
  have eq1 := Equation4362_4512_implies_Equation1 G eq4362 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4320, eq4362, eq4512⟩

theorem AT351_implied_by_long (G : Type*) [Magma G] : AssociativeTheory351_long G -> AssociativeTheory351 G :=
fun ⟨_, _, h4362, h4512⟩ => ⟨h4362, h4512⟩

theorem AT351_equiv (G : Type*) [Magma G] : AssociativeTheory351 G <-> AssociativeTheory351_long G :=
Iff.intro (AT351_implies_long G) (AT351_implied_by_long G)

theorem AT352_implies_long (G : Type*) [Magma G] (h : AssociativeTheory352 G) : AssociativeTheory352_long G := by
  obtain ⟨eq3, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq8 := Equation3_4512_implies_Equation8 G eq3 eq4512
  have eq47 := Equation3_4512_implies_Equation47 G eq3 eq4512
  have eq307 := Equation3_4512_implies_Equation307 G eq3 eq4512
  have eq323 := Equation3_4512_implies_Equation323 G eq3 eq4512
  have eq326 := Equation3_4512_implies_Equation326 G eq3 eq4512
  have eq411 := Equation3_4512_implies_Equation411 G eq3 eq4512
  have eq3253 := Equation3_4512_implies_Equation3253 G eq3 eq4512
  have eq3306 := Equation3_4512_implies_Equation3306 G eq3 eq4512
  have eq3309 := Equation3_4512_implies_Equation3309 G eq3 eq4512
  have eq3316 := Equation3_4512_implies_Equation3316 G eq3 eq4512
  have eq3319 := Equation3_4512_implies_Equation3319 G eq3 eq4512
  have eq4284 := Equation3_4512_implies_Equation4284 G eq3 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq333 := Equation323_4291_4512_implies_Equation333 G eq323 eq4291 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  exact ⟨eq1, eq3, eq8, eq47, eq307, eq323, eq326, eq333, eq411, eq3253, eq3306, eq3309, eq3316, eq3319, eq3346, eq3353, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem AT352_implied_by_long (G : Type*) [Magma G] : AssociativeTheory352_long G -> AssociativeTheory352 G :=
fun ⟨_, h3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h3, h4362, h4512⟩

theorem AT352_equiv (G : Type*) [Magma G] : AssociativeTheory352 G <-> AssociativeTheory352_long G :=
Iff.intro (AT352_implies_long G) (AT352_implied_by_long G)

theorem AT353_implies_long (G : Type*) [Magma G] (h : AssociativeTheory353 G) : AssociativeTheory353_long G := by
  obtain ⟨eq8, eq4362, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4362, eq4512⟩

theorem AT353_implied_by_long (G : Type*) [Magma G] : AssociativeTheory353_long G -> AssociativeTheory353 G :=
fun ⟨_, h8, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h8, h4362, h4512⟩

theorem AT353_equiv (G : Type*) [Magma G] : AssociativeTheory353 G <-> AssociativeTheory353_long G :=
Iff.intro (AT353_implies_long G) (AT353_implied_by_long G)

theorem AT354_implies_long (G : Type*) [Magma G] (h : AssociativeTheory354 G) : AssociativeTheory354_long G := by
  obtain ⟨eq40, eq4362, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4290_4320_4512_implies_Equation4283 G eq4290 eq4320 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4362, eq4512⟩

theorem AT354_implied_by_long (G : Type*) [Magma G] : AssociativeTheory354_long G -> AssociativeTheory354 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h40, h4362, h4512⟩

theorem AT354_equiv (G : Type*) [Magma G] : AssociativeTheory354 G <-> AssociativeTheory354_long G :=
Iff.intro (AT354_implies_long G) (AT354_implied_by_long G)

theorem AT355_implies_long (G : Type*) [Magma G] (h : AssociativeTheory355 G) : AssociativeTheory355_long G := by
  obtain ⟨eq47, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq47, eq4320, eq4362, eq4512⟩

theorem AT355_implied_by_long (G : Type*) [Magma G] : AssociativeTheory355_long G -> AssociativeTheory355 G :=
fun ⟨_, h47, _, h4362, h4512⟩ => ⟨h47, h4362, h4512⟩

theorem AT355_equiv (G : Type*) [Magma G] : AssociativeTheory355 G <-> AssociativeTheory355_long G :=
Iff.intro (AT355_implies_long G) (AT355_implied_by_long G)

theorem AT356_implies_long (G : Type*) [Magma G] (h : AssociativeTheory356 G) : AssociativeTheory356_long G := by
  obtain ⟨eq307, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4320, eq4362, eq4512⟩

theorem AT356_implied_by_long (G : Type*) [Magma G] : AssociativeTheory356_long G -> AssociativeTheory356 G :=
fun ⟨_, h307, _, _, h4362, h4512⟩ => ⟨h307, h4362, h4512⟩

theorem AT356_equiv (G : Type*) [Magma G] : AssociativeTheory356 G <-> AssociativeTheory356_long G :=
Iff.intro (AT356_implies_long G) (AT356_implied_by_long G)

theorem AT357_implies_long (G : Type*) [Magma G] (h : AssociativeTheory357 G) : AssociativeTheory357_long G := by
  obtain ⟨eq40, eq307, eq4362, eq4512⟩ := h
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4290_4320_4512_implies_Equation4283 G eq4290 eq4320 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq309 := Equation3258_4320_4512_implies_Equation309 G eq3258 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq3265 := Equation308_309_4512_implies_Equation3265 G eq308 eq309 eq4512
  have eq3260 := Equation308_309_4512_implies_Equation3260 G eq308 eq309 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4362, eq4512⟩

theorem AT357_implied_by_long (G : Type*) [Magma G] : AssociativeTheory357_long G -> AssociativeTheory357 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h40, h307, h4362, h4512⟩

theorem AT357_equiv (G : Type*) [Magma G] : AssociativeTheory357 G <-> AssociativeTheory357_long G :=
Iff.intro (AT357_implies_long G) (AT357_implied_by_long G)

theorem AT358_implies_long (G : Type*) [Magma G] (h : AssociativeTheory358 G) : AssociativeTheory358_long G := by
  obtain ⟨eq309, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation309_4512_implies_Equation307 G eq309 eq4512
  have eq3253 := Equation309_4512_implies_Equation3253 G eq309 eq4512
  have eq3255 := Equation309_4512_implies_Equation3255 G eq309 eq4512
  have eq3258 := Equation309_4512_implies_Equation3258 G eq309 eq4512
  have eq3261 := Equation309_4512_implies_Equation3261 G eq309 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4284 := Equation309_4512_implies_Equation4284 G eq309 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq4275 := Equation4269_4291_4512_implies_Equation4275 G eq4269 eq4291 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  exact ⟨eq1, eq307, eq309, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT358_implied_by_long (G : Type*) [Magma G] : AssociativeTheory358_long G -> AssociativeTheory358 G :=
fun ⟨_, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h309, h4362, h4512⟩

theorem AT358_equiv (G : Type*) [Magma G] : AssociativeTheory358 G <-> AssociativeTheory358_long G :=
Iff.intro (AT358_implies_long G) (AT358_implied_by_long G)

theorem AT359_implies_long (G : Type*) [Magma G] (h : AssociativeTheory359 G) : AssociativeTheory359_long G := by
  obtain ⟨eq323, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4320, eq4362, eq4512⟩

theorem AT359_implied_by_long (G : Type*) [Magma G] : AssociativeTheory359_long G -> AssociativeTheory359 G :=
fun ⟨_, _, h323, _, _, _, h4362, h4512⟩ => ⟨h323, h4362, h4512⟩

theorem AT359_equiv (G : Type*) [Magma G] : AssociativeTheory359 G <-> AssociativeTheory359_long G :=
Iff.intro (AT359_implies_long G) (AT359_implied_by_long G)

theorem AT360_implies_long (G : Type*) [Magma G] (h : AssociativeTheory360 G) : AssociativeTheory360_long G := by
  obtain ⟨eq326, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq3306 := Equation3346_4512_implies_Equation3306 G eq3346 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  have eq323 := Equation307_3306_4512_implies_Equation323 G eq307 eq3306 eq4512
  have eq333 := Equation307_3353_4512_implies_Equation333 G eq307 eq3353 eq4512
  have eq3309 := Equation323_326_4512_implies_Equation3309 G eq323 eq326 eq4512
  have eq3316 := Equation333_4512_implies_Equation3316 G eq333 eq4512
  have eq4291 := Equation333_4512_implies_Equation4291 G eq333 eq4512
  have eq4284 := Equation4291_4320_4512_implies_Equation4284 G eq4291 eq4320 eq4512
  exact ⟨eq1, eq307, eq323, eq326, eq333, eq3253, eq3306, eq3309, eq3316, eq3319, eq3346, eq3353, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem AT360_implied_by_long (G : Type*) [Magma G] : AssociativeTheory360_long G -> AssociativeTheory360 G :=
fun ⟨_, _, _, h326, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h326, h4362, h4512⟩

theorem AT360_equiv (G : Type*) [Magma G] : AssociativeTheory360 G <-> AssociativeTheory360_long G :=
Iff.intro (AT360_implies_long G) (AT360_implied_by_long G)

theorem AT361_implies_long (G : Type*) [Magma G] (h : AssociativeTheory361 G) : AssociativeTheory361_long G := by
  obtain ⟨eq411, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq411, eq4320, eq4362, eq4512⟩

theorem AT361_implied_by_long (G : Type*) [Magma G] : AssociativeTheory361_long G -> AssociativeTheory361 G :=
fun ⟨_, h411, _, h4362, h4512⟩ => ⟨h411, h4362, h4512⟩

theorem AT361_equiv (G : Type*) [Magma G] : AssociativeTheory361 G <-> AssociativeTheory361_long G :=
Iff.intro (AT361_implies_long G) (AT361_implied_by_long G)

theorem AT362_implies_long (G : Type*) [Magma G] (h : AssociativeTheory362 G) : AssociativeTheory362_long G := by
  obtain ⟨eq3253, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq3253, eq4320, eq4362, eq4512⟩

theorem AT362_implied_by_long (G : Type*) [Magma G] : AssociativeTheory362_long G -> AssociativeTheory362 G :=
fun ⟨_, h3253, _, h4362, h4512⟩ => ⟨h3253, h4362, h4512⟩

theorem AT362_equiv (G : Type*) [Magma G] : AssociativeTheory362 G <-> AssociativeTheory362_long G :=
Iff.intro (AT362_implies_long G) (AT362_implied_by_long G)

theorem AT363_implies_long (G : Type*) [Magma G] (h : AssociativeTheory363 G) : AssociativeTheory363_long G := by
  obtain ⟨eq3261, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq4275, eq4320, eq4362, eq4512⟩

theorem AT363_implied_by_long (G : Type*) [Magma G] : AssociativeTheory363_long G -> AssociativeTheory363 G :=
fun ⟨_, _, h3261, _, _, _, _, h4362, h4512⟩ => ⟨h3261, h4362, h4512⟩

theorem AT363_equiv (G : Type*) [Magma G] : AssociativeTheory363 G <-> AssociativeTheory363_long G :=
Iff.intro (AT363_implies_long G) (AT363_implied_by_long G)

theorem AT364_implies_long (G : Type*) [Magma G] (h : AssociativeTheory364 G) : AssociativeTheory364_long G := by
  obtain ⟨eq3267, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq309 := Equation3255_4320_4512_implies_Equation309 G eq3255 eq4320 eq4512
  have eq40 := Equation3256_4320_4512_implies_Equation40 G eq3256 eq4320 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq312 := Equation3258_4291_4512_implies_Equation312 G eq3258 eq4291 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4272 := Equation4270_4291_4512_implies_Equation4272 G eq4270 eq4291 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4269 := Equation4273_4284_4512_implies_Equation4269 G eq4273 eq4284 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq4283 := Equation4290_4320_4512_implies_Equation4283 G eq4290 eq4320 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4321 := Equation313_4512_implies_Equation4321 G eq313 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4362, eq4512⟩

theorem AT364_implied_by_long (G : Type*) [Magma G] : AssociativeTheory364_long G -> AssociativeTheory364 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h3267, h4362, h4512⟩

theorem AT364_equiv (G : Type*) [Magma G] : AssociativeTheory364 G <-> AssociativeTheory364_long G :=
Iff.intro (AT364_implies_long G) (AT364_implied_by_long G)

theorem AT365_implies_long (G : Type*) [Magma G] (h : AssociativeTheory365 G) : AssociativeTheory365_long G := by
  obtain ⟨eq3300, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation3300_4512_implies_Equation307 G eq3300 eq4512
  have eq312 := Equation3300_4512_implies_Equation312 G eq3300 eq4512
  have eq315 := Equation3300_4512_implies_Equation315 G eq3300 eq4512
  have eq3253 := Equation3300_4512_implies_Equation3253 G eq3300 eq4512
  have eq3255 := Equation3300_4512_implies_Equation3255 G eq3300 eq4512
  have eq3258 := Equation3300_4512_implies_Equation3258 G eq3300 eq4512
  have eq3261 := Equation3300_4512_implies_Equation3261 G eq3300 eq4512
  have eq3264 := Equation3300_4512_implies_Equation3264 G eq3300 eq4512
  have eq3271 := Equation3300_4512_implies_Equation3271 G eq3300 eq4512
  have eq3274 := Equation3300_4512_implies_Equation3274 G eq3300 eq4512
  have eq3278 := Equation3300_4512_implies_Equation3278 G eq3300 eq4512
  have eq3292 := Equation3300_4512_implies_Equation3292 G eq3300 eq4512
  have eq4272 := Equation3300_4512_implies_Equation4272 G eq3300 eq4512
  have eq4275 := Equation3300_4512_implies_Equation4275 G eq3300 eq4512
  have eq4284 := Equation3300_4512_implies_Equation4284 G eq3300 eq4512
  have eq4304 := Equation3300_4512_implies_Equation4304 G eq3300 eq4512
  have eq4269 := Equation4272_4320_4512_implies_Equation4269 G eq4272 eq4320 eq4512
  have eq309 := Equation3255_4320_4512_implies_Equation309 G eq3255 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  exact ⟨eq1, eq307, eq309, eq312, eq315, eq3253, eq3255, eq3258, eq3261, eq3264, eq3271, eq3274, eq3278, eq3292, eq3300, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT365_implied_by_long (G : Type*) [Magma G] : AssociativeTheory365_long G -> AssociativeTheory365 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h3300, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h3300, h4362, h4512⟩

theorem AT365_equiv (G : Type*) [Magma G] : AssociativeTheory365 G <-> AssociativeTheory365_long G :=
Iff.intro (AT365_implies_long G) (AT365_implied_by_long G)

theorem AT366_implies_long (G : Type*) [Magma G] (h : AssociativeTheory366 G) : AssociativeTheory366_long G := by
  obtain ⟨eq3306, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq3253, eq3306, eq4320, eq4362, eq4512⟩

theorem AT366_implied_by_long (G : Type*) [Magma G] : AssociativeTheory366_long G -> AssociativeTheory366 G :=
fun ⟨_, _, h3306, _, h4362, h4512⟩ => ⟨h3306, h4362, h4512⟩

theorem AT366_equiv (G : Type*) [Magma G] : AssociativeTheory366 G <-> AssociativeTheory366_long G :=
Iff.intro (AT366_implies_long G) (AT366_implied_by_long G)

theorem AT367_implies_long (G : Type*) [Magma G] (h : AssociativeTheory367 G) : AssociativeTheory367_long G := by
  obtain ⟨eq3319, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq3306 := Equation3346_4512_implies_Equation3306 G eq3346 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4362, eq4512⟩

theorem AT367_implied_by_long (G : Type*) [Magma G] : AssociativeTheory367_long G -> AssociativeTheory367 G :=
fun ⟨_, _, _, h3319, _, _, _, h4362, h4512⟩ => ⟨h3319, h4362, h4512⟩

theorem AT367_equiv (G : Type*) [Magma G] : AssociativeTheory367 G <-> AssociativeTheory367_long G :=
Iff.intro (AT367_implies_long G) (AT367_implied_by_long G)

theorem AT368_implies_long (G : Type*) [Magma G] (h : AssociativeTheory368 G) : AssociativeTheory368_long G := by
  obtain ⟨eq4268, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4320, eq4362, eq4512⟩

theorem AT368_implied_by_long (G : Type*) [Magma G] : AssociativeTheory368_long G -> AssociativeTheory368 G :=
fun ⟨_, h4268, _, _, _, _, _, h4362, h4512⟩ => ⟨h4268, h4362, h4512⟩

theorem AT368_equiv (G : Type*) [Magma G] : AssociativeTheory368 G <-> AssociativeTheory368_long G :=
Iff.intro (AT368_implies_long G) (AT368_implied_by_long G)

theorem AT369_implies_long (G : Type*) [Magma G] (h : AssociativeTheory369 G) : AssociativeTheory369_long G := by
  obtain ⟨eq4269, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4320, eq4327, eq4362, eq4512⟩

theorem AT369_implied_by_long (G : Type*) [Magma G] : AssociativeTheory369_long G -> AssociativeTheory369 G :=
fun ⟨_, h4269, _, _, _, h4362, h4512⟩ => ⟨h4269, h4362, h4512⟩

theorem AT369_equiv (G : Type*) [Magma G] : AssociativeTheory369 G <-> AssociativeTheory369_long G :=
Iff.intro (AT369_implies_long G) (AT369_implied_by_long G)

theorem AT370_implies_long (G : Type*) [Magma G] (h : AssociativeTheory370 G) : AssociativeTheory370_long G := by
  obtain ⟨eq4268, eq4269, eq4362, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4273 := Equation4275_4283_4512_implies_Equation4273 G eq4275 eq4283 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4362, eq4512⟩

theorem AT370_implied_by_long (G : Type*) [Magma G] : AssociativeTheory370_long G -> AssociativeTheory370 G :=
fun ⟨_, h4268, h4269, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4268, h4269, h4362, h4512⟩

theorem AT370_equiv (G : Type*) [Magma G] : AssociativeTheory370 G <-> AssociativeTheory370_long G :=
Iff.intro (AT370_implies_long G) (AT370_implied_by_long G)

theorem AT371_implies_long (G : Type*) [Magma G] (h : AssociativeTheory371 G) : AssociativeTheory371_long G := by
  obtain ⟨eq4270, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4320, eq4325, eq4362, eq4512⟩

theorem AT371_implied_by_long (G : Type*) [Magma G] : AssociativeTheory371_long G -> AssociativeTheory371 G :=
fun ⟨_, h4270, _, _, _, h4362, h4512⟩ => ⟨h4270, h4362, h4512⟩

theorem AT371_equiv (G : Type*) [Magma G] : AssociativeTheory371 G <-> AssociativeTheory371_long G :=
Iff.intro (AT371_implies_long G) (AT371_implied_by_long G)

theorem AT372_implies_long (G : Type*) [Magma G] (h : AssociativeTheory372 G) : AssociativeTheory372_long G := by
  obtain ⟨eq4269, eq4270, eq4362, eq4512⟩ := h
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4270, eq4272, eq4273, eq4276, eq4279, eq4280, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4362, eq4512⟩

theorem AT372_implied_by_long (G : Type*) [Magma G] : AssociativeTheory372_long G -> AssociativeTheory372 G :=
fun ⟨_, h4269, h4270, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4269, h4270, h4362, h4512⟩

theorem AT372_equiv (G : Type*) [Magma G] : AssociativeTheory372 G <-> AssociativeTheory372_long G :=
Iff.intro (AT372_implies_long G) (AT372_implied_by_long G)

theorem AT373_implies_long (G : Type*) [Magma G] (h : AssociativeTheory373 G) : AssociativeTheory373_long G := by
  obtain ⟨eq4275, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4275, eq4320, eq4362, eq4512⟩

theorem AT373_implied_by_long (G : Type*) [Magma G] : AssociativeTheory373_long G -> AssociativeTheory373 G :=
fun ⟨_, h4275, _, h4362, h4512⟩ => ⟨h4275, h4362, h4512⟩

theorem AT373_equiv (G : Type*) [Magma G] : AssociativeTheory373 G <-> AssociativeTheory373_long G :=
Iff.intro (AT373_implies_long G) (AT373_implied_by_long G)

theorem AT374_implies_long (G : Type*) [Magma G] (h : AssociativeTheory374 G) : AssociativeTheory374_long G := by
  obtain ⟨eq4269, eq4275, eq4362, eq4512⟩ := h
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4284 := Equation4291_4320_4512_implies_Equation4284 G eq4291 eq4320 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4362, eq4512⟩

theorem AT374_implied_by_long (G : Type*) [Magma G] : AssociativeTheory374_long G -> AssociativeTheory374 G :=
fun ⟨_, h4269, _, h4275, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4269, h4275, h4362, h4512⟩

theorem AT374_equiv (G : Type*) [Magma G] : AssociativeTheory374 G <-> AssociativeTheory374_long G :=
Iff.intro (AT374_implies_long G) (AT374_implied_by_long G)

theorem AT375_implies_long (G : Type*) [Magma G] (h : AssociativeTheory375 G) : AssociativeTheory375_long G := by
  obtain ⟨eq4270, eq4275, eq4362, eq4512⟩ := h
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4290 := Equation4297_4512_implies_Equation4290 G eq4297 eq4512
  have eq4283 := Equation4290_4320_4512_implies_Equation4283 G eq4290 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4362, eq4512⟩

theorem AT375_implied_by_long (G : Type*) [Magma G] : AssociativeTheory375_long G -> AssociativeTheory375 G :=
fun ⟨_, h4270, _, h4275, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4270, h4275, h4362, h4512⟩

theorem AT375_equiv (G : Type*) [Magma G] : AssociativeTheory375 G <-> AssociativeTheory375_long G :=
Iff.intro (AT375_implies_long G) (AT375_implied_by_long G)

theorem AT376_implies_long (G : Type*) [Magma G] (h : AssociativeTheory376 G) : AssociativeTheory376_long G := by
  obtain ⟨eq4276, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4276, eq4320, eq4362, eq4512⟩

theorem AT376_implied_by_long (G : Type*) [Magma G] : AssociativeTheory376_long G -> AssociativeTheory376 G :=
fun ⟨_, h4276, _, h4362, h4512⟩ => ⟨h4276, h4362, h4512⟩

theorem AT376_equiv (G : Type*) [Magma G] : AssociativeTheory376 G <-> AssociativeTheory376_long G :=
Iff.intro (AT376_implies_long G) (AT376_implied_by_long G)

theorem AT377_implies_long (G : Type*) [Magma G] (h : AssociativeTheory377 G) : AssociativeTheory377_long G := by
  obtain ⟨eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem AT377_implied_by_long (G : Type*) [Magma G] : AssociativeTheory377_long G -> AssociativeTheory377 G :=
fun ⟨_, h4283, _, _, h4362, h4512⟩ => ⟨h4283, h4362, h4512⟩

theorem AT377_equiv (G : Type*) [Magma G] : AssociativeTheory377 G <-> AssociativeTheory377_long G :=
Iff.intro (AT377_implies_long G) (AT377_implied_by_long G)

theorem AT378_implies_long (G : Type*) [Magma G] (h : AssociativeTheory378 G) : AssociativeTheory378_long G := by
  obtain ⟨eq307, eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem AT378_implied_by_long (G : Type*) [Magma G] : AssociativeTheory378_long G -> AssociativeTheory378 G :=
fun ⟨_, h307, _, h4283, _, _, h4362, h4512⟩ => ⟨h307, h4283, h4362, h4512⟩

theorem AT378_equiv (G : Type*) [Magma G] : AssociativeTheory378 G <-> AssociativeTheory378_long G :=
Iff.intro (AT378_implies_long G) (AT378_implied_by_long G)

theorem AT379_implies_long (G : Type*) [Magma G] (h : AssociativeTheory379 G) : AssociativeTheory379_long G := by
  obtain ⟨eq3253, eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem AT379_implied_by_long (G : Type*) [Magma G] : AssociativeTheory379_long G -> AssociativeTheory379 G :=
fun ⟨_, h3253, h4283, _, _, h4362, h4512⟩ => ⟨h3253, h4283, h4362, h4512⟩

theorem AT379_equiv (G : Type*) [Magma G] : AssociativeTheory379 G <-> AssociativeTheory379_long G :=
Iff.intro (AT379_implies_long G) (AT379_implied_by_long G)

theorem AT380_implies_long (G : Type*) [Magma G] (h : AssociativeTheory380 G) : AssociativeTheory380_long G := by
  obtain ⟨eq4276, eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem AT380_implied_by_long (G : Type*) [Magma G] : AssociativeTheory380_long G -> AssociativeTheory380 G :=
fun ⟨_, h4276, h4283, _, _, h4362, h4512⟩ => ⟨h4276, h4283, h4362, h4512⟩

theorem AT380_equiv (G : Type*) [Magma G] : AssociativeTheory380 G <-> AssociativeTheory380_long G :=
Iff.intro (AT380_implies_long G) (AT380_implied_by_long G)

theorem AT381_implies_long (G : Type*) [Magma G] (h : AssociativeTheory381 G) : AssociativeTheory381_long G := by
  obtain ⟨eq4284, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  exact ⟨eq1, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem AT381_implied_by_long (G : Type*) [Magma G] : AssociativeTheory381_long G -> AssociativeTheory381 G :=
fun ⟨_, h4284, _, _, h4362, h4512⟩ => ⟨h4284, h4362, h4512⟩

theorem AT381_equiv (G : Type*) [Magma G] : AssociativeTheory381 G <-> AssociativeTheory381_long G :=
Iff.intro (AT381_implies_long G) (AT381_implied_by_long G)

theorem AT382_implies_long (G : Type*) [Magma G] (h : AssociativeTheory382 G) : AssociativeTheory382_long G := by
  obtain ⟨eq307, eq4284, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem AT382_implied_by_long (G : Type*) [Magma G] : AssociativeTheory382_long G -> AssociativeTheory382 G :=
fun ⟨_, h307, _, h4284, _, _, h4362, h4512⟩ => ⟨h307, h4284, h4362, h4512⟩

theorem AT382_equiv (G : Type*) [Magma G] : AssociativeTheory382 G <-> AssociativeTheory382_long G :=
Iff.intro (AT382_implies_long G) (AT382_implied_by_long G)

theorem AT383_implies_long (G : Type*) [Magma G] (h : AssociativeTheory383 G) : AssociativeTheory383_long G := by
  obtain ⟨eq4276, eq4284, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem AT383_implied_by_long (G : Type*) [Magma G] : AssociativeTheory383_long G -> AssociativeTheory383 G :=
fun ⟨_, h4276, h4284, _, _, h4362, h4512⟩ => ⟨h4276, h4284, h4362, h4512⟩

theorem AT383_equiv (G : Type*) [Magma G] : AssociativeTheory383 G <-> AssociativeTheory383_long G :=
Iff.intro (AT383_implies_long G) (AT383_implied_by_long G)

theorem AT384_implies_long (G : Type*) [Magma G] (h : AssociativeTheory384 G) : AssociativeTheory384_long G := by
  obtain ⟨eq4283, eq4284, eq4362, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT384_implied_by_long (G : Type*) [Magma G] : AssociativeTheory384_long G -> AssociativeTheory384 G :=
fun ⟨_, h4283, h4284, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4283, h4284, h4362, h4512⟩

theorem AT384_equiv (G : Type*) [Magma G] : AssociativeTheory384 G <-> AssociativeTheory384_long G :=
Iff.intro (AT384_implies_long G) (AT384_implied_by_long G)

theorem AT385_implies_long (G : Type*) [Magma G] (h : AssociativeTheory385 G) : AssociativeTheory385_long G := by
  obtain ⟨eq307, eq4283, eq4284, eq4362, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT385_implied_by_long (G : Type*) [Magma G] : AssociativeTheory385_long G -> AssociativeTheory385 G :=
fun ⟨_, h307, _, h4283, h4284, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h307, h4283, h4284, h4362, h4512⟩

theorem AT385_equiv (G : Type*) [Magma G] : AssociativeTheory385 G <-> AssociativeTheory385_long G :=
Iff.intro (AT385_implies_long G) (AT385_implied_by_long G)

theorem AT386_implies_long (G : Type*) [Magma G] (h : AssociativeTheory386 G) : AssociativeTheory386_long G := by
  obtain ⟨eq4276, eq4283, eq4284, eq4362, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT386_implied_by_long (G : Type*) [Magma G] : AssociativeTheory386_long G -> AssociativeTheory386 G :=
fun ⟨_, h4276, h4283, h4284, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4276, h4283, h4284, h4362, h4512⟩

theorem AT386_equiv (G : Type*) [Magma G] : AssociativeTheory386 G <-> AssociativeTheory386_long G :=
Iff.intro (AT386_implies_long G) (AT386_implied_by_long G)

theorem AT387_implies_long (G : Type*) [Magma G] (h : AssociativeTheory387 G) : AssociativeTheory387_long G := by
  obtain ⟨eq4293, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4293, eq4320, eq4362, eq4512⟩

theorem AT387_implied_by_long (G : Type*) [Magma G] : AssociativeTheory387_long G -> AssociativeTheory387 G :=
fun ⟨_, h4293, _, h4362, h4512⟩ => ⟨h4293, h4362, h4512⟩

theorem AT387_equiv (G : Type*) [Magma G] : AssociativeTheory387 G <-> AssociativeTheory387_long G :=
Iff.intro (AT387_implies_long G) (AT387_implied_by_long G)

theorem AT388_implies_long (G : Type*) [Magma G] (h : AssociativeTheory388 G) : AssociativeTheory388_long G := by
  obtain ⟨eq4269, eq4293, eq4362, eq4512⟩ := h
  have eq4273 := Equation4269_4293_4512_implies_Equation4273 G eq4269 eq4293 eq4512
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4270 := Equation4273_4320_4512_implies_Equation4270 G eq4273 eq4320 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  have eq4314 := Equation4320_4321_4512_implies_Equation4314 G eq4320 eq4321 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4269, eq4270, eq4272, eq4273, eq4276, eq4279, eq4280, eq4293, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4362, eq4512⟩

theorem AT388_implied_by_long (G : Type*) [Magma G] : AssociativeTheory388_long G -> AssociativeTheory388 G :=
fun ⟨_, h4269, _, _, _, _, _, _, h4293, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4269, h4293, h4362, h4512⟩

theorem AT388_equiv (G : Type*) [Magma G] : AssociativeTheory388 G <-> AssociativeTheory388_long G :=
Iff.intro (AT388_implies_long G) (AT388_implied_by_long G)

theorem AT389_implies_long (G : Type*) [Magma G] (h : AssociativeTheory389 G) : AssociativeTheory389_long G := by
  obtain ⟨eq4276, eq4293, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4320, eq4362, eq4512⟩

theorem AT389_implied_by_long (G : Type*) [Magma G] : AssociativeTheory389_long G -> AssociativeTheory389 G :=
fun ⟨_, h4276, h4293, _, h4362, h4512⟩ => ⟨h4276, h4293, h4362, h4512⟩

theorem AT389_equiv (G : Type*) [Magma G] : AssociativeTheory389 G <-> AssociativeTheory389_long G :=
Iff.intro (AT389_implies_long G) (AT389_implied_by_long G)

theorem AT390_implies_long (G : Type*) [Magma G] (h : AssociativeTheory390 G) : AssociativeTheory390_long G := by
  obtain ⟨eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT390_implied_by_long (G : Type*) [Magma G] : AssociativeTheory390_long G -> AssociativeTheory390 G :=
fun ⟨_, h4314, _, _, _, h4362, h4512⟩ => ⟨h4314, h4362, h4512⟩

theorem AT390_equiv (G : Type*) [Magma G] : AssociativeTheory390 G <-> AssociativeTheory390_long G :=
Iff.intro (AT390_implies_long G) (AT390_implied_by_long G)

theorem AT391_implies_long (G : Type*) [Magma G] (h : AssociativeTheory391 G) : AssociativeTheory391_long G := by
  obtain ⟨eq307, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT391_implied_by_long (G : Type*) [Magma G] : AssociativeTheory391_long G -> AssociativeTheory391 G :=
fun ⟨_, h307, _, h4314, _, _, _, h4362, h4512⟩ => ⟨h307, h4314, h4362, h4512⟩

theorem AT391_equiv (G : Type*) [Magma G] : AssociativeTheory391 G <-> AssociativeTheory391_long G :=
Iff.intro (AT391_implies_long G) (AT391_implied_by_long G)

theorem AT392_implies_long (G : Type*) [Magma G] (h : AssociativeTheory392 G) : AssociativeTheory392_long G := by
  obtain ⟨eq4268, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT392_implied_by_long (G : Type*) [Magma G] : AssociativeTheory392_long G -> AssociativeTheory392 G :=
fun ⟨_, h4268, _, _, _, _, h4314, _, _, _, h4362, h4512⟩ => ⟨h4268, h4314, h4362, h4512⟩

theorem AT392_equiv (G : Type*) [Magma G] : AssociativeTheory392 G <-> AssociativeTheory392_long G :=
Iff.intro (AT392_implies_long G) (AT392_implied_by_long G)

theorem AT393_implies_long (G : Type*) [Magma G] (h : AssociativeTheory393 G) : AssociativeTheory393_long G := by
  obtain ⟨eq4276, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT393_implied_by_long (G : Type*) [Magma G] : AssociativeTheory393_long G -> AssociativeTheory393 G :=
fun ⟨_, h4276, h4314, _, _, _, h4362, h4512⟩ => ⟨h4276, h4314, h4362, h4512⟩

theorem AT393_equiv (G : Type*) [Magma G] : AssociativeTheory393 G <-> AssociativeTheory393_long G :=
Iff.intro (AT393_implies_long G) (AT393_implied_by_long G)

theorem AT394_implies_long (G : Type*) [Magma G] (h : AssociativeTheory394 G) : AssociativeTheory394_long G := by
  obtain ⟨eq4293, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT394_implied_by_long (G : Type*) [Magma G] : AssociativeTheory394_long G -> AssociativeTheory394 G :=
fun ⟨_, h4293, h4314, _, _, _, h4362, h4512⟩ => ⟨h4293, h4314, h4362, h4512⟩

theorem AT394_equiv (G : Type*) [Magma G] : AssociativeTheory394 G <-> AssociativeTheory394_long G :=
Iff.intro (AT394_implies_long G) (AT394_implied_by_long G)

theorem AT395_implies_long (G : Type*) [Magma G] (h : AssociativeTheory395 G) : AssociativeTheory395_long G := by
  obtain ⟨eq4276, eq4293, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem AT395_implied_by_long (G : Type*) [Magma G] : AssociativeTheory395_long G -> AssociativeTheory395 G :=
fun ⟨_, h4276, h4293, h4314, _, _, _, h4362, h4512⟩ => ⟨h4276, h4293, h4314, h4362, h4512⟩

theorem AT395_equiv (G : Type*) [Magma G] : AssociativeTheory395 G <-> AssociativeTheory395_long G :=
Iff.intro (AT395_implies_long G) (AT395_implied_by_long G)

theorem AT396_implies_long (G : Type*) [Magma G] (h : AssociativeTheory396 G) : AssociativeTheory396_long G := by
  obtain ⟨eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT396_implied_by_long (G : Type*) [Magma G] : AssociativeTheory396_long G -> AssociativeTheory396 G :=
fun ⟨_, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4358, h4362, h4512⟩

theorem AT396_equiv (G : Type*) [Magma G] : AssociativeTheory396 G <-> AssociativeTheory396_long G :=
Iff.intro (AT396_implies_long G) (AT396_implied_by_long G)

theorem AT397_implies_long (G : Type*) [Magma G] (h : AssociativeTheory397 G) : AssociativeTheory397_long G := by
  obtain ⟨eq40, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT397_implied_by_long (G : Type*) [Magma G] : AssociativeTheory397_long G -> AssociativeTheory397 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h40, h4358, h4362, h4512⟩

theorem AT397_equiv (G : Type*) [Magma G] : AssociativeTheory397 G <-> AssociativeTheory397_long G :=
Iff.intro (AT397_implies_long G) (AT397_implied_by_long G)

theorem AT398_implies_long (G : Type*) [Magma G] (h : AssociativeTheory398 G) : AssociativeTheory398_long G := by
  obtain ⟨eq307, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT398_implied_by_long (G : Type*) [Magma G] : AssociativeTheory398_long G -> AssociativeTheory398 G :=
fun ⟨_, h307, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h307, h4358, h4362, h4512⟩

theorem AT398_equiv (G : Type*) [Magma G] : AssociativeTheory398 G <-> AssociativeTheory398_long G :=
Iff.intro (AT398_implies_long G) (AT398_implied_by_long G)

theorem AT399_implies_long (G : Type*) [Magma G] (h : AssociativeTheory399 G) : AssociativeTheory399_long G := by
  obtain ⟨eq40, eq307, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq3264 := Equation308_4369_4512_implies_Equation3264 G eq308 eq4369 eq4512
  have eq3265 := Equation308_4369_4512_implies_Equation3265 G eq308 eq4369 eq4512
  have eq3260 := Equation308_4369_4512_implies_Equation3260 G eq308 eq4369 eq4512
  have eq309 := Equation3255_4320_4512_implies_Equation309 G eq3255 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT399_implied_by_long (G : Type*) [Magma G] : AssociativeTheory399_long G -> AssociativeTheory399 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h40, h307, h4358, h4362, h4512⟩

theorem AT399_equiv (G : Type*) [Magma G] : AssociativeTheory399 G <-> AssociativeTheory399_long G :=
Iff.intro (AT399_implies_long G) (AT399_implied_by_long G)

theorem AT400_implies_long (G : Type*) [Magma G] (h : AssociativeTheory400 G) : AssociativeTheory400_long G := by
  obtain ⟨eq3253, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT400_implied_by_long (G : Type*) [Magma G] : AssociativeTheory400_long G -> AssociativeTheory400 G :=
fun ⟨_, h3253, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h3253, h4358, h4362, h4512⟩

theorem AT400_equiv (G : Type*) [Magma G] : AssociativeTheory400 G <-> AssociativeTheory400_long G :=
Iff.intro (AT400_implies_long G) (AT400_implied_by_long G)

theorem AT401_implies_long (G : Type*) [Magma G] (h : AssociativeTheory401 G) : AssociativeTheory401_long G := by
  obtain ⟨eq3267, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq309 := Equation3255_4320_4512_implies_Equation309 G eq3255 eq4320 eq4512
  have eq40 := Equation3256_4320_4512_implies_Equation40 G eq3256 eq4320 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq312 := Equation3258_4291_4512_implies_Equation312 G eq3258 eq4291 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT401_implied_by_long (G : Type*) [Magma G] : AssociativeTheory401_long G -> AssociativeTheory401 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h3267, h4358, h4362, h4512⟩

theorem AT401_equiv (G : Type*) [Magma G] : AssociativeTheory401 G <-> AssociativeTheory401_long G :=
Iff.intro (AT401_implies_long G) (AT401_implied_by_long G)

theorem AT402_implies_long (G : Type*) [Magma G] (h : AssociativeTheory402 G) : AssociativeTheory402_long G := by
  obtain ⟨eq4268, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4270 := Equation4275_4290_4512_implies_Equation4270 G eq4275 eq4290 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq4284 := Equation4290_4293_4512_implies_Equation4284 G eq4290 eq4293 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT402_implied_by_long (G : Type*) [Magma G] : AssociativeTheory402_long G -> AssociativeTheory402 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4268, h4358, h4362, h4512⟩

theorem AT402_equiv (G : Type*) [Magma G] : AssociativeTheory402 G <-> AssociativeTheory402_long G :=
Iff.intro (AT402_implies_long G) (AT402_implied_by_long G)

theorem AT403_implies_long (G : Type*) [Magma G] (h : AssociativeTheory403 G) : AssociativeTheory403_long G := by
  obtain ⟨eq4270, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT403_implied_by_long (G : Type*) [Magma G] : AssociativeTheory403_long G -> AssociativeTheory403 G :=
fun ⟨_, h4270, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4270, h4358, h4362, h4512⟩

theorem AT403_equiv (G : Type*) [Magma G] : AssociativeTheory403 G <-> AssociativeTheory403_long G :=
Iff.intro (AT403_implies_long G) (AT403_implied_by_long G)

theorem AT404_implies_long (G : Type*) [Magma G] (h : AssociativeTheory404 G) : AssociativeTheory404_long G := by
  obtain ⟨eq4276, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT404_implied_by_long (G : Type*) [Magma G] : AssociativeTheory404_long G -> AssociativeTheory404 G :=
fun ⟨_, h4276, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4276, h4358, h4362, h4512⟩

theorem AT404_equiv (G : Type*) [Magma G] : AssociativeTheory404 G <-> AssociativeTheory404_long G :=
Iff.intro (AT404_implies_long G) (AT404_implied_by_long G)

theorem AT405_implies_long (G : Type*) [Magma G] (h : AssociativeTheory405 G) : AssociativeTheory405_long G := by
  obtain ⟨eq4284, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT405_implied_by_long (G : Type*) [Magma G] : AssociativeTheory405_long G -> AssociativeTheory405 G :=
fun ⟨_, _, h4284, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4284, h4358, h4362, h4512⟩

theorem AT405_equiv (G : Type*) [Magma G] : AssociativeTheory405 G <-> AssociativeTheory405_long G :=
Iff.intro (AT405_implies_long G) (AT405_implied_by_long G)

theorem AT406_implies_long (G : Type*) [Magma G] (h : AssociativeTheory406 G) : AssociativeTheory406_long G := by
  obtain ⟨eq307, eq4284, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT406_implied_by_long (G : Type*) [Magma G] : AssociativeTheory406_long G -> AssociativeTheory406 G :=
fun ⟨_, h307, _, _, h4284, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h307, h4284, h4358, h4362, h4512⟩

theorem AT406_equiv (G : Type*) [Magma G] : AssociativeTheory406 G <-> AssociativeTheory406_long G :=
Iff.intro (AT406_implies_long G) (AT406_implied_by_long G)

theorem AT407_implies_long (G : Type*) [Magma G] (h : AssociativeTheory407 G) : AssociativeTheory407_long G := by
  obtain ⟨eq4276, eq4284, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem AT407_implied_by_long (G : Type*) [Magma G] : AssociativeTheory407_long G -> AssociativeTheory407 G :=
fun ⟨_, h4276, _, h4284, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4276, h4284, h4358, h4362, h4512⟩

theorem AT407_equiv (G : Type*) [Magma G] : AssociativeTheory407 G <-> AssociativeTheory407_long G :=
Iff.intro (AT407_implies_long G) (AT407_implied_by_long G)

theorem AT408_implies_long (G : Type*) [Magma G] (h : AssociativeTheory408 G) : AssociativeTheory408_long G := by
  obtain ⟨eq4364, eq4512⟩ := h
  have eq1 := Equation4364_4512_implies_Equation1 G eq4364 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem AT408_implied_by_long (G : Type*) [Magma G] : AssociativeTheory408_long G -> AssociativeTheory408 G :=
fun ⟨_, _, _, _, h4364, h4512⟩ => ⟨h4364, h4512⟩

theorem AT408_equiv (G : Type*) [Magma G] : AssociativeTheory408 G <-> AssociativeTheory408_long G :=
Iff.intro (AT408_implies_long G) (AT408_implied_by_long G)

theorem AT409_implies_long (G : Type*) [Magma G] (h : AssociativeTheory409 G) : AssociativeTheory409_long G := by
  obtain ⟨eq40, eq4364, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4364, eq4512⟩

theorem AT409_implied_by_long (G : Type*) [Magma G] : AssociativeTheory409_long G -> AssociativeTheory409 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h40, h4364, h4512⟩

theorem AT409_equiv (G : Type*) [Magma G] : AssociativeTheory409 G <-> AssociativeTheory409_long G :=
Iff.intro (AT409_implies_long G) (AT409_implied_by_long G)

theorem AT410_implies_long (G : Type*) [Magma G] (h : AssociativeTheory410 G) : AssociativeTheory410_long G := by
  obtain ⟨eq307, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem AT410_implied_by_long (G : Type*) [Magma G] : AssociativeTheory410_long G -> AssociativeTheory410 G :=
fun ⟨_, h307, _, _, _, _, h4364, h4512⟩ => ⟨h307, h4364, h4512⟩

theorem AT410_equiv (G : Type*) [Magma G] : AssociativeTheory410 G <-> AssociativeTheory410_long G :=
Iff.intro (AT410_implies_long G) (AT410_implied_by_long G)

theorem AT411_implies_long (G : Type*) [Magma G] (h : AssociativeTheory411 G) : AssociativeTheory411_long G := by
  obtain ⟨eq40, eq307, eq4364, eq4512⟩ := h
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq309 := Equation3258_4320_4512_implies_Equation309 G eq3258 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq3265 := Equation308_309_4512_implies_Equation3265 G eq308 eq309 eq4512
  have eq3260 := Equation308_309_4512_implies_Equation3260 G eq308 eq309 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4364, eq4512⟩

theorem AT411_implied_by_long (G : Type*) [Magma G] : AssociativeTheory411_long G -> AssociativeTheory411 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h40, h307, h4364, h4512⟩

theorem AT411_equiv (G : Type*) [Magma G] : AssociativeTheory411 G <-> AssociativeTheory411_long G :=
Iff.intro (AT411_implies_long G) (AT411_implied_by_long G)

theorem AT412_implies_long (G : Type*) [Magma G] (h : AssociativeTheory412 G) : AssociativeTheory412_long G := by
  obtain ⟨eq3253, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem AT412_implied_by_long (G : Type*) [Magma G] : AssociativeTheory412_long G -> AssociativeTheory412 G :=
fun ⟨_, h3253, _, _, _, h4364, h4512⟩ => ⟨h3253, h4364, h4512⟩

theorem AT412_equiv (G : Type*) [Magma G] : AssociativeTheory412 G <-> AssociativeTheory412_long G :=
Iff.intro (AT412_implies_long G) (AT412_implied_by_long G)

theorem AT413_implies_long (G : Type*) [Magma G] (h : AssociativeTheory413 G) : AssociativeTheory413_long G := by
  obtain ⟨eq3267, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq40 := Equation3255_4290_4512_implies_Equation40 G eq3255 eq4290 eq4512
  have eq309 := Equation3255_4320_4512_implies_Equation309 G eq3255 eq4320 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4364, eq4512⟩

theorem AT413_implied_by_long (G : Type*) [Magma G] : AssociativeTheory413_long G -> AssociativeTheory413 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h3267, h4364, h4512⟩

theorem AT413_equiv (G : Type*) [Magma G] : AssociativeTheory413 G <-> AssociativeTheory413_long G :=
Iff.intro (AT413_implies_long G) (AT413_implied_by_long G)

theorem AT414_implies_long (G : Type*) [Magma G] (h : AssociativeTheory414 G) : AssociativeTheory414_long G := by
  obtain ⟨eq4268, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4364, eq4512⟩

theorem AT414_implied_by_long (G : Type*) [Magma G] : AssociativeTheory414_long G -> AssociativeTheory414 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4268, h4364, h4512⟩

theorem AT414_equiv (G : Type*) [Magma G] : AssociativeTheory414 G <-> AssociativeTheory414_long G :=
Iff.intro (AT414_implies_long G) (AT414_implied_by_long G)

theorem AT415_implies_long (G : Type*) [Magma G] (h : AssociativeTheory415 G) : AssociativeTheory415_long G := by
  obtain ⟨eq4270, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4364, eq4512⟩

theorem AT415_implied_by_long (G : Type*) [Magma G] : AssociativeTheory415_long G -> AssociativeTheory415 G :=
fun ⟨_, h4270, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4270, h4364, h4512⟩

theorem AT415_equiv (G : Type*) [Magma G] : AssociativeTheory415 G <-> AssociativeTheory415_long G :=
Iff.intro (AT415_implies_long G) (AT415_implied_by_long G)

theorem AT416_implies_long (G : Type*) [Magma G] (h : AssociativeTheory416 G) : AssociativeTheory416_long G := by
  obtain ⟨eq4276, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem AT416_implied_by_long (G : Type*) [Magma G] : AssociativeTheory416_long G -> AssociativeTheory416 G :=
fun ⟨_, h4276, _, _, _, h4364, h4512⟩ => ⟨h4276, h4364, h4512⟩

theorem AT416_equiv (G : Type*) [Magma G] : AssociativeTheory416 G <-> AssociativeTheory416_long G :=
Iff.intro (AT416_implies_long G) (AT416_implied_by_long G)

theorem AT417_implies_long (G : Type*) [Magma G] (h : AssociativeTheory417 G) : AssociativeTheory417_long G := by
  obtain ⟨eq4284, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4364, eq4512⟩

theorem AT417_implied_by_long (G : Type*) [Magma G] : AssociativeTheory417_long G -> AssociativeTheory417 G :=
fun ⟨_, _, h4284, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4284, h4364, h4512⟩

theorem AT417_equiv (G : Type*) [Magma G] : AssociativeTheory417 G <-> AssociativeTheory417_long G :=
Iff.intro (AT417_implies_long G) (AT417_implied_by_long G)

theorem AT418_implies_long (G : Type*) [Magma G] (h : AssociativeTheory418 G) : AssociativeTheory418_long G := by
  obtain ⟨eq307, eq4284, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4364, eq4512⟩

theorem AT418_implied_by_long (G : Type*) [Magma G] : AssociativeTheory418_long G -> AssociativeTheory418 G :=
fun ⟨_, h307, _, _, h4284, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h307, h4284, h4364, h4512⟩

theorem AT418_equiv (G : Type*) [Magma G] : AssociativeTheory418 G <-> AssociativeTheory418_long G :=
Iff.intro (AT418_implies_long G) (AT418_implied_by_long G)

theorem AT419_implies_long (G : Type*) [Magma G] (h : AssociativeTheory419 G) : AssociativeTheory419_long G := by
  obtain ⟨eq4276, eq4284, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4364, eq4512⟩

theorem AT419_implied_by_long (G : Type*) [Magma G] : AssociativeTheory419_long G -> AssociativeTheory419 G :=
fun ⟨_, h4276, _, h4284, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4276, h4284, h4364, h4512⟩

theorem AT419_equiv (G : Type*) [Magma G] : AssociativeTheory419 G <-> AssociativeTheory419_long G :=
Iff.intro (AT419_implies_long G) (AT419_implied_by_long G)

theorem AT420_implies_long (G : Type*) [Magma G] (h : AssociativeTheory420 G) : AssociativeTheory420_long G := by
  obtain ⟨eq4369, eq4512⟩ := h
  have eq1 := Equation4369_4512_implies_Equation1 G eq4369 eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4290, eq4369, eq4512⟩

theorem AT420_implied_by_long (G : Type*) [Magma G] : AssociativeTheory420_long G -> AssociativeTheory420 G :=
fun ⟨_, _, h4369, h4512⟩ => ⟨h4369, h4512⟩

theorem AT420_equiv (G : Type*) [Magma G] : AssociativeTheory420 G <-> AssociativeTheory420_long G :=
Iff.intro (AT420_implies_long G) (AT420_implied_by_long G)

theorem AT421_implies_long (G : Type*) [Magma G] (h : AssociativeTheory421 G) : AssociativeTheory421_long G := by
  obtain ⟨eq40, eq4369, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4275, eq4290, eq4297, eq4369, eq4512⟩

theorem AT421_implied_by_long (G : Type*) [Magma G] : AssociativeTheory421_long G -> AssociativeTheory421 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h40, h4369, h4512⟩

theorem AT421_equiv (G : Type*) [Magma G] : AssociativeTheory421 G <-> AssociativeTheory421_long G :=
Iff.intro (AT421_implies_long G) (AT421_implied_by_long G)

theorem AT422_implies_long (G : Type*) [Magma G] (h : AssociativeTheory422 G) : AssociativeTheory422_long G := by
  obtain ⟨eq307, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4290, eq4369, eq4512⟩

theorem AT422_implied_by_long (G : Type*) [Magma G] : AssociativeTheory422_long G -> AssociativeTheory422 G :=
fun ⟨_, h307, _, _, h4369, h4512⟩ => ⟨h307, h4369, h4512⟩

theorem AT422_equiv (G : Type*) [Magma G] : AssociativeTheory422 G <-> AssociativeTheory422_long G :=
Iff.intro (AT422_implies_long G) (AT422_implied_by_long G)

theorem AT423_implies_long (G : Type*) [Magma G] (h : AssociativeTheory423 G) : AssociativeTheory423_long G := by
  obtain ⟨eq40, eq307, eq4369, eq4512⟩ := h
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq3258 := Equation307_3261_4512_implies_Equation3258 G eq307 eq3261 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  have eq310 := Equation316_4512_implies_Equation310 G eq316 eq4512
  have eq315 := Equation316_4512_implies_Equation315 G eq316 eq4512
  have eq3255 := Equation316_4512_implies_Equation3255 G eq316 eq4512
  have eq4268 := Equation316_4512_implies_Equation4268 G eq316 eq4512
  have eq4272 := Equation316_4512_implies_Equation4272 G eq316 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4277 := Equation316_4512_implies_Equation4277 G eq316 eq4512
  have eq4280 := Equation316_4512_implies_Equation4280 G eq316 eq4512
  have eq4288 := Equation316_4512_implies_Equation4288 G eq316 eq4512
  have eq4293 := Equation316_4512_implies_Equation4293 G eq316 eq4512
  have eq4299 := Equation316_4512_implies_Equation4299 G eq316 eq4512
  have eq4304 := Equation316_4512_implies_Equation4304 G eq316 eq4512
  have eq4343 := Equation316_4512_implies_Equation4343 G eq316 eq4512
  have eq3264 := Equation308_4369_4512_implies_Equation3264 G eq308 eq4369 eq4512
  have eq3265 := Equation308_4369_4512_implies_Equation3265 G eq308 eq4369 eq4512
  have eq3260 := Equation308_4369_4512_implies_Equation3260 G eq308 eq4369 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4369, eq4512⟩

theorem AT423_implied_by_long (G : Type*) [Magma G] : AssociativeTheory423_long G -> AssociativeTheory423 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h40, h307, h4369, h4512⟩

theorem AT423_equiv (G : Type*) [Magma G] : AssociativeTheory423 G <-> AssociativeTheory423_long G :=
Iff.intro (AT423_implies_long G) (AT423_implied_by_long G)

theorem AT424_implies_long (G : Type*) [Magma G] (h : AssociativeTheory424 G) : AssociativeTheory424_long G := by
  obtain ⟨eq309, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq307 := Equation309_4512_implies_Equation307 G eq309 eq4512
  have eq3253 := Equation309_4512_implies_Equation3253 G eq309 eq4512
  have eq3255 := Equation309_4512_implies_Equation3255 G eq309 eq4512
  have eq3258 := Equation309_4512_implies_Equation3258 G eq309 eq4512
  have eq3261 := Equation309_4512_implies_Equation3261 G eq309 eq4512
  have eq3264 := Equation309_4512_implies_Equation3264 G eq309 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4284 := Equation309_4512_implies_Equation4284 G eq309 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq40 := Equation3255_4290_4512_implies_Equation40 G eq3255 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4272 := Equation4270_4293_4512_implies_Equation4272 G eq4270 eq4293 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4268 := Equation4270_4284_4512_implies_Equation4268 G eq4270 eq4284 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_3256_4512_implies_Equation308 G eq307 eq3256 eq4512
  have eq310 := Equation3275_4512_implies_Equation310 G eq3275 eq4512
  have eq315 := Equation3275_4512_implies_Equation315 G eq3275 eq4512
  have eq4276 := Equation3275_4512_implies_Equation4276 G eq3275 eq4512
  have eq4277 := Equation3275_4512_implies_Equation4277 G eq3275 eq4512
  have eq4280 := Equation3275_4512_implies_Equation4280 G eq3275 eq4512
  have eq4288 := Equation3275_4512_implies_Equation4288 G eq3275 eq4512
  have eq4299 := Equation3275_4512_implies_Equation4299 G eq3275 eq4512
  have eq4304 := Equation3275_4512_implies_Equation4304 G eq3275 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  have eq3260 := Equation313_4512_implies_Equation3260 G eq313 eq4512
  have eq3265 := Equation313_4512_implies_Equation3265 G eq313 eq4512
  have eq3273 := Equation313_4512_implies_Equation3273 G eq313 eq4512
  have eq3274 := Equation313_4512_implies_Equation3274 G eq313 eq4512
  have eq3290 := Equation313_4512_implies_Equation3290 G eq313 eq4512
  have eq3292 := Equation313_4512_implies_Equation3292 G eq313 eq4512
  have eq4283 := Equation313_4512_implies_Equation4283 G eq313 eq4512
  have eq4286 := Equation313_4512_implies_Equation4286 G eq313 eq4512
  have eq4291 := Equation313_4512_implies_Equation4291 G eq313 eq4512
  have eq4301 := Equation313_4512_implies_Equation4301 G eq313 eq4512
  have eq4314 := Equation313_4512_implies_Equation4314 G eq313 eq4512
  have eq4320 := Equation313_4512_implies_Equation4320 G eq313 eq4512
  have eq4327 := Equation313_4512_implies_Equation4327 G eq313 eq4512
  have eq4331 := Equation313_4512_implies_Equation4331 G eq313 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4369, eq4512⟩

theorem AT424_implied_by_long (G : Type*) [Magma G] : AssociativeTheory424_long G -> AssociativeTheory424 G :=
fun ⟨_, _, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h309, h4369, h4512⟩

theorem AT424_equiv (G : Type*) [Magma G] : AssociativeTheory424 G <-> AssociativeTheory424_long G :=
Iff.intro (AT424_implies_long G) (AT424_implied_by_long G)

theorem AT425_implies_long (G : Type*) [Magma G] (h : AssociativeTheory425 G) : AssociativeTheory425_long G := by
  obtain ⟨eq3253, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq3253, eq4290, eq4369, eq4512⟩

theorem AT425_implied_by_long (G : Type*) [Magma G] : AssociativeTheory425_long G -> AssociativeTheory425 G :=
fun ⟨_, h3253, _, h4369, h4512⟩ => ⟨h3253, h4369, h4512⟩

theorem AT425_equiv (G : Type*) [Magma G] : AssociativeTheory425 G <-> AssociativeTheory425_long G :=
Iff.intro (AT425_implies_long G) (AT425_implied_by_long G)

theorem AT426_implies_long (G : Type*) [Magma G] (h : AssociativeTheory426 G) : AssociativeTheory426_long G := by
  obtain ⟨eq3267, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq40 := Equation3255_4290_4512_implies_Equation40 G eq3255 eq4290 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq3274 := Equation3277_4512_implies_Equation3274 G eq3277 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4369, eq4512⟩

theorem AT426_implied_by_long (G : Type*) [Magma G] : AssociativeTheory426_long G -> AssociativeTheory426 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h3267, h4369, h4512⟩

theorem AT426_equiv (G : Type*) [Magma G] : AssociativeTheory426 G <-> AssociativeTheory426_long G :=
Iff.intro (AT426_implies_long G) (AT426_implied_by_long G)

theorem AT427_implies_long (G : Type*) [Magma G] (h : AssociativeTheory427 G) : AssociativeTheory427_long G := by
  obtain ⟨eq309, eq3267, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4269 := Equation309_4512_implies_Equation4269 G eq309 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq40 := Equation3256_4290_4512_implies_Equation40 G eq3256 eq4290 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq313 := Equation40_309_4512_implies_Equation313 G eq40 eq309 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4291 := Equation4283_4293_4512_implies_Equation4291 G eq4283 eq4293 eq4512
  have eq3274 := Equation309_312_4512_implies_Equation3274 G eq309 eq312 eq4512
  have eq3292 := Equation309_312_4512_implies_Equation3292 G eq309 eq312 eq4512
  have eq4276 := Equation316_4512_implies_Equation4276 G eq316 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq309, eq310, eq312, eq313, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4369, eq4512⟩

theorem AT427_implied_by_long (G : Type*) [Magma G] : AssociativeTheory427_long G -> AssociativeTheory427 G :=
fun ⟨_, _, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h309, h3267, h4369, h4512⟩

theorem AT427_equiv (G : Type*) [Magma G] : AssociativeTheory427 G <-> AssociativeTheory427_long G :=
Iff.intro (AT427_implies_long G) (AT427_implied_by_long G)

theorem AT428_implies_long (G : Type*) [Magma G] (h : AssociativeTheory428 G) : AssociativeTheory428_long G := by
  obtain ⟨eq4268, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4270 := Equation4299_4512_implies_Equation4270 G eq4299 eq4512
  have eq4275 := Equation4299_4512_implies_Equation4275 G eq4299 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4277 := Equation4299_4512_implies_Equation4277 G eq4299 eq4512
  have eq4280 := Equation4299_4512_implies_Equation4280 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4288 := Equation4299_4512_implies_Equation4288 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4297 := Equation4299_4512_implies_Equation4297 G eq4299 eq4512
  have eq4304 := Equation4299_4512_implies_Equation4304 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  exact ⟨eq1, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4343, eq4369, eq4512⟩

theorem AT428_implied_by_long (G : Type*) [Magma G] : AssociativeTheory428_long G -> AssociativeTheory428 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4268, h4369, h4512⟩

theorem AT428_equiv (G : Type*) [Magma G] : AssociativeTheory428 G <-> AssociativeTheory428_long G :=
Iff.intro (AT428_implies_long G) (AT428_implied_by_long G)

theorem AT429_implies_long (G : Type*) [Magma G] (h : AssociativeTheory429 G) : AssociativeTheory429_long G := by
  obtain ⟨eq4269, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4290, eq4321, eq4369, eq4512⟩

theorem AT429_implied_by_long (G : Type*) [Magma G] : AssociativeTheory429_long G -> AssociativeTheory429 G :=
fun ⟨_, h4269, _, _, _, _, _, h4369, h4512⟩ => ⟨h4269, h4369, h4512⟩

theorem AT429_equiv (G : Type*) [Magma G] : AssociativeTheory429 G <-> AssociativeTheory429_long G :=
Iff.intro (AT429_implies_long G) (AT429_implied_by_long G)

theorem AT430_implies_long (G : Type*) [Magma G] (h : AssociativeTheory430 G) : AssociativeTheory430_long G := by
  obtain ⟨eq4268, eq4269, eq4369, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4301 := Equation4268_4273_4512_implies_Equation4301 G eq4268 eq4273 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4270 := Equation4272_4273_4512_implies_Equation4270 G eq4272 eq4273 eq4512
  have eq4275 := Equation4273_4283_4512_implies_Equation4275 G eq4273 eq4283 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4276 := Equation4299_4512_implies_Equation4276 G eq4299 eq4512
  have eq4284 := Equation4299_4512_implies_Equation4284 G eq4299 eq4512
  have eq4293 := Equation4299_4512_implies_Equation4293 G eq4299 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  have eq4291 := Equation4301_4512_implies_Equation4291 G eq4301 eq4512
  have eq4321 := Equation4301_4512_implies_Equation4321 G eq4301 eq4512
  have eq4331 := Equation4269_4280_4512_implies_Equation4331 G eq4269 eq4280 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4272, eq4273, eq4275, eq4276, eq4277, eq4279, eq4280, eq4283, eq4284, eq4286, eq4288, eq4290, eq4291, eq4293, eq4296, eq4297, eq4299, eq4301, eq4304, eq4305, eq4314, eq4318, eq4320, eq4321, eq4325, eq4327, eq4331, eq4343, eq4369, eq4512⟩

theorem AT430_implied_by_long (G : Type*) [Magma G] : AssociativeTheory430_long G -> AssociativeTheory430 G :=
fun ⟨_, h4268, h4269, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4268, h4269, h4369, h4512⟩

theorem AT430_equiv (G : Type*) [Magma G] : AssociativeTheory430 G <-> AssociativeTheory430_long G :=
Iff.intro (AT430_implies_long G) (AT430_implied_by_long G)

theorem AT431_implies_long (G : Type*) [Magma G] (h : AssociativeTheory431 G) : AssociativeTheory431_long G := by
  obtain ⟨eq4270, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  exact ⟨eq1, eq4270, eq4275, eq4290, eq4297, eq4369, eq4512⟩

theorem AT431_implied_by_long (G : Type*) [Magma G] : AssociativeTheory431_long G -> AssociativeTheory431 G :=
fun ⟨_, h4270, _, _, _, h4369, h4512⟩ => ⟨h4270, h4369, h4512⟩

theorem AT431_equiv (G : Type*) [Magma G] : AssociativeTheory431 G <-> AssociativeTheory431_long G :=
Iff.intro (AT431_implies_long G) (AT431_implied_by_long G)

theorem AT432_implies_long (G : Type*) [Magma G] (h : AssociativeTheory432 G) : AssociativeTheory432_long G := by
  obtain ⟨eq4273, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4273, eq4290, eq4369, eq4512⟩

theorem AT432_implied_by_long (G : Type*) [Magma G] : AssociativeTheory432_long G -> AssociativeTheory432 G :=
fun ⟨_, h4273, _, h4369, h4512⟩ => ⟨h4273, h4369, h4512⟩

theorem AT432_equiv (G : Type*) [Magma G] : AssociativeTheory432 G <-> AssociativeTheory432_long G :=
Iff.intro (AT432_implies_long G) (AT432_implied_by_long G)

theorem AT433_implies_long (G : Type*) [Magma G] (h : AssociativeTheory433 G) : AssociativeTheory433_long G := by
  obtain ⟨eq40, eq4273, eq4369, eq4512⟩ := h
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  exact ⟨eq1, eq40, eq3253, eq3256, eq3259, eq3261, eq3271, eq3278, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4369, eq4512⟩

theorem AT433_implied_by_long (G : Type*) [Magma G] : AssociativeTheory433_long G -> AssociativeTheory433 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, h4273, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h40, h4273, h4369, h4512⟩

theorem AT433_equiv (G : Type*) [Magma G] : AssociativeTheory433 G <-> AssociativeTheory433_long G :=
Iff.intro (AT433_implies_long G) (AT433_implied_by_long G)

theorem AT434_implies_long (G : Type*) [Magma G] (h : AssociativeTheory434 G) : AssociativeTheory434_long G := by
  obtain ⟨eq4270, eq4273, eq4369, eq4512⟩ := h
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  have eq4283 := Equation4290_4320_4512_implies_Equation4283 G eq4290 eq4320 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4369, eq4512⟩

theorem AT434_implied_by_long (G : Type*) [Magma G] : AssociativeTheory434_long G -> AssociativeTheory434 G :=
fun ⟨_, h4270, h4273, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4270, h4273, h4369, h4512⟩

theorem AT434_equiv (G : Type*) [Magma G] : AssociativeTheory434 G <-> AssociativeTheory434_long G :=
Iff.intro (AT434_implies_long G) (AT434_implied_by_long G)

theorem AT435_implies_long (G : Type*) [Magma G] (h : AssociativeTheory435 G) : AssociativeTheory435_long G := by
  obtain ⟨eq4276, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4276, eq4290, eq4369, eq4512⟩

theorem AT435_implied_by_long (G : Type*) [Magma G] : AssociativeTheory435_long G -> AssociativeTheory435 G :=
fun ⟨_, h4276, _, h4369, h4512⟩ => ⟨h4276, h4369, h4512⟩

theorem AT435_equiv (G : Type*) [Magma G] : AssociativeTheory435 G <-> AssociativeTheory435_long G :=
Iff.intro (AT435_implies_long G) (AT435_implied_by_long G)

theorem AT436_implies_long (G : Type*) [Magma G] (h : AssociativeTheory436 G) : AssociativeTheory436_long G := by
  obtain ⟨eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem AT436_implied_by_long (G : Type*) [Magma G] : AssociativeTheory436_long G -> AssociativeTheory436 G :=
fun ⟨_, h4283, _, _, h4369, h4512⟩ => ⟨h4283, h4369, h4512⟩

theorem AT436_equiv (G : Type*) [Magma G] : AssociativeTheory436 G <-> AssociativeTheory436_long G :=
Iff.intro (AT436_implies_long G) (AT436_implied_by_long G)

theorem AT437_implies_long (G : Type*) [Magma G] (h : AssociativeTheory437 G) : AssociativeTheory437_long G := by
  obtain ⟨eq307, eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem AT437_implied_by_long (G : Type*) [Magma G] : AssociativeTheory437_long G -> AssociativeTheory437 G :=
fun ⟨_, h307, _, h4283, _, _, h4369, h4512⟩ => ⟨h307, h4283, h4369, h4512⟩

theorem AT437_equiv (G : Type*) [Magma G] : AssociativeTheory437 G <-> AssociativeTheory437_long G :=
Iff.intro (AT437_implies_long G) (AT437_implied_by_long G)

theorem AT438_implies_long (G : Type*) [Magma G] (h : AssociativeTheory438 G) : AssociativeTheory438_long G := by
  obtain ⟨eq3253, eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem AT438_implied_by_long (G : Type*) [Magma G] : AssociativeTheory438_long G -> AssociativeTheory438 G :=
fun ⟨_, h3253, h4283, _, _, h4369, h4512⟩ => ⟨h3253, h4283, h4369, h4512⟩

theorem AT438_equiv (G : Type*) [Magma G] : AssociativeTheory438 G <-> AssociativeTheory438_long G :=
Iff.intro (AT438_implies_long G) (AT438_implied_by_long G)

theorem AT439_implies_long (G : Type*) [Magma G] (h : AssociativeTheory439 G) : AssociativeTheory439_long G := by
  obtain ⟨eq4276, eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem AT439_implied_by_long (G : Type*) [Magma G] : AssociativeTheory439_long G -> AssociativeTheory439 G :=
fun ⟨_, h4276, h4283, _, _, h4369, h4512⟩ => ⟨h4276, h4283, h4369, h4512⟩

theorem AT439_equiv (G : Type*) [Magma G] : AssociativeTheory439 G <-> AssociativeTheory439_long G :=
Iff.intro (AT439_implies_long G) (AT439_implied_by_long G)

theorem AT440_implies_long (G : Type*) [Magma G] (h : AssociativeTheory440 G) : AssociativeTheory440_long G := by
  obtain ⟨eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4343, eq4369, eq4512⟩

theorem AT440_implied_by_long (G : Type*) [Magma G] : AssociativeTheory440_long G -> AssociativeTheory440 G :=
fun ⟨_, h4284, _, _, _, h4369, h4512⟩ => ⟨h4284, h4369, h4512⟩

theorem AT440_equiv (G : Type*) [Magma G] : AssociativeTheory440 G <-> AssociativeTheory440_long G :=
Iff.intro (AT440_implies_long G) (AT440_implied_by_long G)

theorem AT441_implies_long (G : Type*) [Magma G] (h : AssociativeTheory441 G) : AssociativeTheory441_long G := by
  obtain ⟨eq307, eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4343, eq4369, eq4512⟩

theorem AT441_implied_by_long (G : Type*) [Magma G] : AssociativeTheory441_long G -> AssociativeTheory441 G :=
fun ⟨_, h307, _, h4284, _, _, _, h4369, h4512⟩ => ⟨h307, h4284, h4369, h4512⟩

theorem AT441_equiv (G : Type*) [Magma G] : AssociativeTheory441 G <-> AssociativeTheory441_long G :=
Iff.intro (AT441_implies_long G) (AT441_implied_by_long G)

theorem AT442_implies_long (G : Type*) [Magma G] (h : AssociativeTheory442 G) : AssociativeTheory442_long G := by
  obtain ⟨eq4269, eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem AT442_implied_by_long (G : Type*) [Magma G] : AssociativeTheory442_long G -> AssociativeTheory442 G :=
fun ⟨_, h4269, _, _, _, h4284, _, _, _, _, h4369, h4512⟩ => ⟨h4269, h4284, h4369, h4512⟩

theorem AT442_equiv (G : Type*) [Magma G] : AssociativeTheory442 G <-> AssociativeTheory442_long G :=
Iff.intro (AT442_implies_long G) (AT442_implied_by_long G)

theorem AT443_implies_long (G : Type*) [Magma G] (h : AssociativeTheory443 G) : AssociativeTheory443_long G := by
  obtain ⟨eq4276, eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4343, eq4369, eq4512⟩

theorem AT443_implied_by_long (G : Type*) [Magma G] : AssociativeTheory443_long G -> AssociativeTheory443 G :=
fun ⟨_, h4276, h4284, _, _, _, h4369, h4512⟩ => ⟨h4276, h4284, h4369, h4512⟩

theorem AT443_equiv (G : Type*) [Magma G] : AssociativeTheory443 G <-> AssociativeTheory443_long G :=
Iff.intro (AT443_implies_long G) (AT443_implied_by_long G)

theorem AT444_implies_long (G : Type*) [Magma G] (h : AssociativeTheory444 G) : AssociativeTheory444_long G := by
  obtain ⟨eq4283, eq4284, eq4369, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4369, eq4512⟩

theorem AT444_implied_by_long (G : Type*) [Magma G] : AssociativeTheory444_long G -> AssociativeTheory444 G :=
fun ⟨_, h4283, h4284, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4283, h4284, h4369, h4512⟩

theorem AT444_equiv (G : Type*) [Magma G] : AssociativeTheory444 G <-> AssociativeTheory444_long G :=
Iff.intro (AT444_implies_long G) (AT444_implied_by_long G)

theorem AT445_implies_long (G : Type*) [Magma G] (h : AssociativeTheory445 G) : AssociativeTheory445_long G := by
  obtain ⟨eq307, eq4283, eq4284, eq4369, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4369, eq4512⟩

theorem AT445_implied_by_long (G : Type*) [Magma G] : AssociativeTheory445_long G -> AssociativeTheory445 G :=
fun ⟨_, h307, _, h4283, h4284, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h307, h4283, h4284, h4369, h4512⟩

theorem AT445_equiv (G : Type*) [Magma G] : AssociativeTheory445 G <-> AssociativeTheory445_long G :=
Iff.intro (AT445_implies_long G) (AT445_implied_by_long G)

theorem AT446_implies_long (G : Type*) [Magma G] (h : AssociativeTheory446 G) : AssociativeTheory446_long G := by
  obtain ⟨eq4276, eq4283, eq4284, eq4369, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4369, eq4512⟩

theorem AT446_implied_by_long (G : Type*) [Magma G] : AssociativeTheory446_long G -> AssociativeTheory446 G :=
fun ⟨_, h4276, h4283, h4284, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4276, h4283, h4284, h4369, h4512⟩

theorem AT446_equiv (G : Type*) [Magma G] : AssociativeTheory446 G <-> AssociativeTheory446_long G :=
Iff.intro (AT446_implies_long G) (AT446_implied_by_long G)

theorem AT447_implies_long (G : Type*) [Magma G] (h : AssociativeTheory447 G) : AssociativeTheory447_long G := by
  obtain ⟨eq4291, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  exact ⟨eq1, eq4290, eq4291, eq4314, eq4369, eq4512⟩

theorem AT447_implied_by_long (G : Type*) [Magma G] : AssociativeTheory447_long G -> AssociativeTheory447 G :=
fun ⟨_, _, h4291, _, h4369, h4512⟩ => ⟨h4291, h4369, h4512⟩

theorem AT447_equiv (G : Type*) [Magma G] : AssociativeTheory447 G <-> AssociativeTheory447_long G :=
Iff.intro (AT447_implies_long G) (AT447_implied_by_long G)

theorem AT448_implies_long (G : Type*) [Magma G] (h : AssociativeTheory448 G) : AssociativeTheory448_long G := by
  obtain ⟨eq4276, eq4291, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4290, eq4291, eq4314, eq4369, eq4512⟩

theorem AT448_implied_by_long (G : Type*) [Magma G] : AssociativeTheory448_long G -> AssociativeTheory448 G :=
fun ⟨_, h4276, _, h4291, _, h4369, h4512⟩ => ⟨h4276, h4291, h4369, h4512⟩

theorem AT448_equiv (G : Type*) [Magma G] : AssociativeTheory448 G <-> AssociativeTheory448_long G :=
Iff.intro (AT448_implies_long G) (AT448_implied_by_long G)

theorem AT449_implies_long (G : Type*) [Magma G] (h : AssociativeTheory449 G) : AssociativeTheory449_long G := by
  obtain ⟨eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4290, eq4321, eq4369, eq4512⟩

theorem AT449_implied_by_long (G : Type*) [Magma G] : AssociativeTheory449_long G -> AssociativeTheory449 G :=
fun ⟨_, _, h4321, h4369, h4512⟩ => ⟨h4321, h4369, h4512⟩

theorem AT449_equiv (G : Type*) [Magma G] : AssociativeTheory449 G <-> AssociativeTheory449_long G :=
Iff.intro (AT449_implies_long G) (AT449_implied_by_long G)

theorem AT450_implies_long (G : Type*) [Magma G] (h : AssociativeTheory450 G) : AssociativeTheory450_long G := by
  obtain ⟨eq40, eq4321, eq4369, eq4512⟩ := h
  have eq3264 := Equation40_4321_4512_implies_Equation3264 G eq40 eq4321 eq4512
  have eq1 := Equation40_4512_implies_Equation1 G eq40 eq4512
  have eq3253 := Equation40_4512_implies_Equation3253 G eq40 eq4512
  have eq3256 := Equation40_4512_implies_Equation3256 G eq40 eq4512
  have eq3259 := Equation40_4512_implies_Equation3259 G eq40 eq4512
  have eq3261 := Equation40_4512_implies_Equation3261 G eq40 eq4512
  have eq3271 := Equation40_4512_implies_Equation3271 G eq40 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq4270 := Equation40_4512_implies_Equation4270 G eq40 eq4512
  have eq4275 := Equation40_4512_implies_Equation4275 G eq40 eq4512
  have eq4290 := Equation40_4512_implies_Equation4290 G eq40 eq4512
  have eq4297 := Equation40_4512_implies_Equation4297 G eq40 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq4268 := Equation4275_4321_4512_implies_Equation4268 G eq4275 eq4321 eq4512
  have eq307 := Equation3253_4321_4512_implies_Equation307 G eq3253 eq4321 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_3278_4512_implies_Equation312 G eq307 eq3278 eq4512
  have eq308 := Equation307_4268_4512_implies_Equation308 G eq307 eq4268 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq310 := Equation3275_4512_implies_Equation310 G eq3275 eq4512
  have eq315 := Equation3275_4512_implies_Equation315 G eq3275 eq4512
  have eq4276 := Equation3275_4512_implies_Equation4276 G eq3275 eq4512
  have eq3265 := Equation308_4369_4512_implies_Equation3265 G eq308 eq4369 eq4512
  have eq3260 := Equation308_4369_4512_implies_Equation3260 G eq308 eq4369 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq3274 := Equation3290_4512_implies_Equation3274 G eq3290 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3271, eq3273, eq3274, eq3275, eq3278, eq3290, eq3292, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4369, eq4512⟩

theorem AT450_implied_by_long (G : Type*) [Magma G] : AssociativeTheory450_long G -> AssociativeTheory450 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h40, h4321, h4369, h4512⟩

theorem AT450_equiv (G : Type*) [Magma G] : AssociativeTheory450 G <-> AssociativeTheory450_long G :=
Iff.intro (AT450_implies_long G) (AT450_implied_by_long G)

theorem AT451_implies_long (G : Type*) [Magma G] (h : AssociativeTheory451 G) : AssociativeTheory451_long G := by
  obtain ⟨eq307, eq4321, eq4369, eq4512⟩ := h
  have eq4293 := Equation307_4321_4369_4512_implies_Equation4293 G eq307 eq4321 eq4369 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4284 := Equation4290_4293_4512_implies_Equation4284 G eq4290 eq4293 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem AT451_implied_by_long (G : Type*) [Magma G] : AssociativeTheory451_long G -> AssociativeTheory451 G :=
fun ⟨_, h307, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h307, h4321, h4369, h4512⟩

theorem AT451_equiv (G : Type*) [Magma G] : AssociativeTheory451 G <-> AssociativeTheory451_long G :=
Iff.intro (AT451_implies_long G) (AT451_implied_by_long G)

theorem AT452_implies_long (G : Type*) [Magma G] (h : AssociativeTheory452 G) : AssociativeTheory452_long G := by
  obtain ⟨eq3267, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3267_4512_implies_Equation307 G eq3267 eq4512
  have eq308 := Equation3267_4512_implies_Equation308 G eq3267 eq4512
  have eq310 := Equation3267_4512_implies_Equation310 G eq3267 eq4512
  have eq3253 := Equation3267_4512_implies_Equation3253 G eq3267 eq4512
  have eq3255 := Equation3267_4512_implies_Equation3255 G eq3267 eq4512
  have eq3256 := Equation3267_4512_implies_Equation3256 G eq3267 eq4512
  have eq3258 := Equation3267_4512_implies_Equation3258 G eq3267 eq4512
  have eq3259 := Equation3267_4512_implies_Equation3259 G eq3267 eq4512
  have eq3260 := Equation3267_4512_implies_Equation3260 G eq3267 eq4512
  have eq3261 := Equation3267_4512_implies_Equation3261 G eq3267 eq4512
  have eq3264 := Equation3267_4512_implies_Equation3264 G eq3267 eq4512
  have eq3265 := Equation3267_4512_implies_Equation3265 G eq3267 eq4512
  have eq4268 := Equation3267_4512_implies_Equation4268 G eq3267 eq4512
  have eq4270 := Equation3267_4512_implies_Equation4270 G eq3267 eq4512
  have eq4284 := Equation3267_4512_implies_Equation4284 G eq3267 eq4512
  have eq4288 := Equation3267_4512_implies_Equation4288 G eq3267 eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq40 := Equation3255_4290_4512_implies_Equation40 G eq3255 eq4290 eq4512
  have eq3275 := Equation40_3264_4512_implies_Equation3275 G eq40 eq3264 eq4512
  have eq3290 := Equation40_3265_4512_implies_Equation3290 G eq40 eq3265 eq4512
  have eq3277 := Equation40_3267_4512_implies_Equation3277 G eq40 eq3267 eq4512
  have eq316 := Equation40_307_4512_implies_Equation316 G eq40 eq307 eq4512
  have eq3273 := Equation40_3260_4512_implies_Equation3273 G eq40 eq3260 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3271 := Equation3253_4275_4512_implies_Equation3271 G eq3253 eq4275 eq4512
  have eq3278 := Equation40_4512_implies_Equation3278 G eq40 eq4512
  have eq315 := Equation312_4284_4512_implies_Equation315 G eq312 eq4284 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq3292 := Equation3273_4512_implies_Equation3292 G eq3273 eq4512
  have eq3274 := Equation3277_4512_implies_Equation3274 G eq3277 eq4512
  have eq3300 := Equation3277_4512_implies_Equation3300 G eq3277 eq4512
  exact ⟨eq1, eq40, eq307, eq308, eq310, eq312, eq315, eq316, eq3253, eq3255, eq3256, eq3258, eq3259, eq3260, eq3261, eq3264, eq3265, eq3267, eq3271, eq3273, eq3274, eq3275, eq3277, eq3278, eq3290, eq3292, eq3300, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4369, eq4512⟩

theorem AT452_implied_by_long (G : Type*) [Magma G] : AssociativeTheory452_long G -> AssociativeTheory452 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h3267, h4321, h4369, h4512⟩

theorem AT452_equiv (G : Type*) [Magma G] : AssociativeTheory452 G <-> AssociativeTheory452_long G :=
Iff.intro (AT452_implies_long G) (AT452_implied_by_long G)

theorem AT453_implies_long (G : Type*) [Magma G] (h : AssociativeTheory453 G) : AssociativeTheory453_long G := by
  obtain ⟨eq4268, eq4321, eq4369, eq4512⟩ := h
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4270 := Equation4275_4290_4512_implies_Equation4270 G eq4275 eq4290 eq4512
  have eq4272 := Equation4268_4290_4512_implies_Equation4272 G eq4268 eq4290 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4299 := Equation4268_4272_4512_implies_Equation4299 G eq4268 eq4272 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  have eq4284 := Equation4290_4293_4512_implies_Equation4284 G eq4290 eq4293 eq4512
  have eq4343 := Equation4299_4512_implies_Equation4343 G eq4299 eq4512
  exact ⟨eq1, eq4268, eq4270, eq4272, eq4275, eq4276, eq4277, eq4280, eq4284, eq4288, eq4290, eq4293, eq4297, eq4299, eq4304, eq4321, eq4343, eq4369, eq4512⟩

theorem AT453_implied_by_long (G : Type*) [Magma G] : AssociativeTheory453_long G -> AssociativeTheory453 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h4268, h4321, h4369, h4512⟩

theorem AT453_equiv (G : Type*) [Magma G] : AssociativeTheory453 G <-> AssociativeTheory453_long G :=
Iff.intro (AT453_implies_long G) (AT453_implied_by_long G)

theorem AT454_implies_long (G : Type*) [Magma G] (h : AssociativeTheory454 G) : AssociativeTheory454_long G := by
  obtain ⟨eq4276, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4276, eq4290, eq4321, eq4369, eq4512⟩

theorem AT454_implied_by_long (G : Type*) [Magma G] : AssociativeTheory454_long G -> AssociativeTheory454 G :=
fun ⟨_, h4276, _, h4321, h4369, h4512⟩ => ⟨h4276, h4321, h4369, h4512⟩

theorem AT454_equiv (G : Type*) [Magma G] : AssociativeTheory454 G <-> AssociativeTheory454_long G :=
Iff.intro (AT454_implies_long G) (AT454_implied_by_long G)

theorem AT455_implies_long (G : Type*) [Magma G] (h : AssociativeTheory455 G) : AssociativeTheory455_long G := by
  obtain ⟨eq4284, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem AT455_implied_by_long (G : Type*) [Magma G] : AssociativeTheory455_long G -> AssociativeTheory455 G :=
fun ⟨_, h4284, _, _, h4321, _, h4369, h4512⟩ => ⟨h4284, h4321, h4369, h4512⟩

theorem AT455_equiv (G : Type*) [Magma G] : AssociativeTheory455 G <-> AssociativeTheory455_long G :=
Iff.intro (AT455_implies_long G) (AT455_implied_by_long G)

theorem AT456_implies_long (G : Type*) [Magma G] (h : AssociativeTheory456 G) : AssociativeTheory456_long G := by
  obtain ⟨eq4276, eq4284, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem AT456_implied_by_long (G : Type*) [Magma G] : AssociativeTheory456_long G -> AssociativeTheory456 G :=
fun ⟨_, h4276, h4284, _, _, h4321, _, h4369, h4512⟩ => ⟨h4276, h4284, h4321, h4369, h4512⟩

theorem AT456_equiv (G : Type*) [Magma G] : AssociativeTheory456 G <-> AssociativeTheory456_long G :=
Iff.intro (AT456_implies_long G) (AT456_implied_by_long G)

