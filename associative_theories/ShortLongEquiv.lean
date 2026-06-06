import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.ConjunctionRepresentatives
import associative_theories.ConjunctionRepresentativesLong
import associative_theories.ConjecturesOneImpli
import associative_theories.ConjecturesTwo
import associative_theories.OneImpliDeduced

/- Generated file proving equivalence of conjunction representatives -/

open Conjectures


theorem CC1_implies_long (G : Type*) [Magma G] (h : ConjunctionClass1 G) : ConjunctionClass1_long G := by
  constructor
  rw [Equation1]; intros; rfl
  exact h

theorem CC1_implied_by_long (G : Type*) [Magma G] : ConjunctionClass1_long G -> ConjunctionClass1 G :=
fun ⟨_, h4512⟩ => h4512

theorem CC1_equiv (G : Type*) [Magma G] : ConjunctionClass1 G <-> ConjunctionClass1_long G :=
Iff.intro (CC1_implies_long G) (CC1_implied_by_long G)

theorem CC2_implies_long (G : Type*) [Magma G] (h : ConjunctionClass2 G) : ConjunctionClass2_long G := by
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

theorem CC2_implied_by_long (G : Type*) [Magma G] : ConjunctionClass2_long G -> ConjunctionClass2 G :=
fun ⟨_, h2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h2, h4512⟩

theorem CC2_equiv (G : Type*) [Magma G] : ConjunctionClass2 G <-> ConjunctionClass2_long G :=
Iff.intro (CC2_implies_long G) (CC2_implied_by_long G)

theorem CC3_implies_long (G : Type*) [Magma G] (h : ConjunctionClass3 G) : ConjunctionClass3_long G := by
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

theorem CC3_implied_by_long (G : Type*) [Magma G] : ConjunctionClass3_long G -> ConjunctionClass3 G :=
fun ⟨_, h3, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h4512⟩

theorem CC3_equiv (G : Type*) [Magma G] : ConjunctionClass3 G <-> ConjunctionClass3_long G :=
Iff.intro (CC3_implies_long G) (CC3_implied_by_long G)

theorem CC4_implies_long (G : Type*) [Magma G] (h : ConjunctionClass4 G) : ConjunctionClass4_long G := by
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

theorem CC4_implied_by_long (G : Type*) [Magma G] : ConjunctionClass4_long G -> ConjunctionClass4 G :=
fun ⟨_, _, h4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4, h4512⟩

theorem CC4_equiv (G : Type*) [Magma G] : ConjunctionClass4 G <-> ConjunctionClass4_long G :=
Iff.intro (CC4_implies_long G) (CC4_implied_by_long G)

theorem CC5_implies_long (G : Type*) [Magma G] (h : ConjunctionClass5 G) : ConjunctionClass5_long G := by
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

theorem CC5_implied_by_long (G : Type*) [Magma G] : ConjunctionClass5_long G -> ConjunctionClass5 G :=
fun ⟨_, _, h5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h5, h4512⟩

theorem CC5_equiv (G : Type*) [Magma G] : ConjunctionClass5 G <-> ConjunctionClass5_long G :=
Iff.intro (CC5_implies_long G) (CC5_implied_by_long G)

theorem CC6_implies_long (G : Type*) [Magma G] (h : ConjunctionClass6 G) : ConjunctionClass6_long G := by
  obtain ⟨eq8, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq4512⟩

theorem CC6_implied_by_long (G : Type*) [Magma G] : ConjunctionClass6_long G -> ConjunctionClass6 G :=
fun ⟨_, h8, _, _, _, _, h4512⟩ => ⟨h8, h4512⟩

theorem CC6_equiv (G : Type*) [Magma G] : ConjunctionClass6 G <-> ConjunctionClass6_long G :=
Iff.intro (CC6_implies_long G) (CC6_implied_by_long G)

theorem CC7_implies_long (G : Type*) [Magma G] (h : ConjunctionClass7 G) : ConjunctionClass7_long G := by
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

theorem CC7_implied_by_long (G : Type*) [Magma G] : ConjunctionClass7_long G -> ConjunctionClass7 G :=
fun ⟨_, _, _, h10, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h10, h4512⟩

theorem CC7_equiv (G : Type*) [Magma G] : ConjunctionClass7 G <-> ConjunctionClass7_long G :=
Iff.intro (CC7_implies_long G) (CC7_implied_by_long G)

theorem CC8_implies_long (G : Type*) [Magma G] (h : ConjunctionClass8 G) : ConjunctionClass8_long G := by
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

theorem CC8_implied_by_long (G : Type*) [Magma G] : ConjunctionClass8_long G -> ConjunctionClass8 G :=
fun ⟨_, _, h11, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h11, h4512⟩

theorem CC8_equiv (G : Type*) [Magma G] : ConjunctionClass8 G <-> ConjunctionClass8_long G :=
Iff.intro (CC8_implies_long G) (CC8_implied_by_long G)

theorem CC9_implies_long (G : Type*) [Magma G] (h : ConjunctionClass9 G) : ConjunctionClass9_long G := by
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

theorem CC9_implied_by_long (G : Type*) [Magma G] : ConjunctionClass9_long G -> ConjunctionClass9 G :=
fun ⟨_, _, _, h14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h14, h4512⟩

theorem CC9_equiv (G : Type*) [Magma G] : ConjunctionClass9 G <-> ConjunctionClass9_long G :=
Iff.intro (CC9_implies_long G) (CC9_implied_by_long G)

theorem CC10_implies_long (G : Type*) [Magma G] (h : ConjunctionClass10 G) : ConjunctionClass10_long G := by
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

theorem CC10_implied_by_long (G : Type*) [Magma G] : ConjunctionClass10_long G -> ConjunctionClass10 G :=
fun ⟨_, _, h16, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h16, h4512⟩

theorem CC10_equiv (G : Type*) [Magma G] : ConjunctionClass10 G <-> ConjunctionClass10_long G :=
Iff.intro (CC10_implies_long G) (CC10_implied_by_long G)

theorem CC11_implies_long (G : Type*) [Magma G] (h : ConjunctionClass11 G) : ConjunctionClass11_long G := by
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

theorem CC11_implied_by_long (G : Type*) [Magma G] : ConjunctionClass11_long G -> ConjunctionClass11 G :=
fun ⟨_, h38, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h38, h4512⟩

theorem CC11_equiv (G : Type*) [Magma G] : ConjunctionClass11 G <-> ConjunctionClass11_long G :=
Iff.intro (CC11_implies_long G) (CC11_implied_by_long G)

theorem CC12_implies_long (G : Type*) [Magma G] (h : ConjunctionClass12 G) : ConjunctionClass12_long G := by
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

theorem CC12_implied_by_long (G : Type*) [Magma G] : ConjunctionClass12_long G -> ConjunctionClass12 G :=
fun ⟨_, h39, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h39, h4512⟩

theorem CC12_equiv (G : Type*) [Magma G] : ConjunctionClass12 G <-> ConjunctionClass12_long G :=
Iff.intro (CC12_implies_long G) (CC12_implied_by_long G)

theorem CC13_implies_long (G : Type*) [Magma G] (h : ConjunctionClass13 G) : ConjunctionClass13_long G := by
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

theorem CC13_implied_by_long (G : Type*) [Magma G] : ConjunctionClass13_long G -> ConjunctionClass13 G :=
fun ⟨_, h38, h39, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h38, h39, h4512⟩

theorem CC13_equiv (G : Type*) [Magma G] : ConjunctionClass13 G <-> ConjunctionClass13_long G :=
Iff.intro (CC13_implies_long G) (CC13_implied_by_long G)

theorem CC14_implies_long (G : Type*) [Magma G] (h : ConjunctionClass14 G) : ConjunctionClass14_long G := by
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

theorem CC14_implied_by_long (G : Type*) [Magma G] : ConjunctionClass14_long G -> ConjunctionClass14 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h4512⟩

theorem CC14_equiv (G : Type*) [Magma G] : ConjunctionClass14 G <-> ConjunctionClass14_long G :=
Iff.intro (CC14_implies_long G) (CC14_implied_by_long G)

theorem CC15_implies_long (G : Type*) [Magma G] (h : ConjunctionClass15 G) : ConjunctionClass15_long G := by
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

theorem CC15_implied_by_long (G : Type*) [Magma G] : ConjunctionClass15_long G -> ConjunctionClass15 G :=
fun ⟨_, h43, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4512⟩

theorem CC15_equiv (G : Type*) [Magma G] : ConjunctionClass15 G <-> ConjunctionClass15_long G :=
Iff.intro (CC15_implies_long G) (CC15_implied_by_long G)

theorem CC16_implies_long (G : Type*) [Magma G] (h : ConjunctionClass16 G) : ConjunctionClass16_long G := by
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

theorem CC16_implied_by_long (G : Type*) [Magma G] : ConjunctionClass16_long G -> ConjunctionClass16 G :=
fun ⟨_, h3, _, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h43, h4512⟩

theorem CC16_equiv (G : Type*) [Magma G] : ConjunctionClass16 G <-> ConjunctionClass16_long G :=
Iff.intro (CC16_implies_long G) (CC16_implied_by_long G)

theorem CC17_implies_long (G : Type*) [Magma G] (h : ConjunctionClass17 G) : ConjunctionClass17_long G := by
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

theorem CC17_implied_by_long (G : Type*) [Magma G] : ConjunctionClass17_long G -> ConjunctionClass17 G :=
fun ⟨_, h8, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h8, h43, h4512⟩

theorem CC17_equiv (G : Type*) [Magma G] : ConjunctionClass17 G <-> ConjunctionClass17_long G :=
Iff.intro (CC17_implies_long G) (CC17_implied_by_long G)

theorem CC18_implies_long (G : Type*) [Magma G] (h : ConjunctionClass18 G) : ConjunctionClass18_long G := by
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

theorem CC18_implied_by_long (G : Type*) [Magma G] : ConjunctionClass18_long G -> ConjunctionClass18 G :=
fun ⟨_, h40, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h43, h4512⟩

theorem CC18_equiv (G : Type*) [Magma G] : ConjunctionClass18 G <-> ConjunctionClass18_long G :=
Iff.intro (CC18_implies_long G) (CC18_implied_by_long G)

theorem CC19_implies_long (G : Type*) [Magma G] (h : ConjunctionClass19 G) : ConjunctionClass19_long G := by
  obtain ⟨eq47, eq4512⟩ := h
  have eq1 := Equation47_4512_implies_Equation1 G eq47 eq4512
  exact ⟨eq1, eq47, eq4512⟩

theorem CC19_implied_by_long (G : Type*) [Magma G] : ConjunctionClass19_long G -> ConjunctionClass19 G :=
fun ⟨_, h47, h4512⟩ => ⟨h47, h4512⟩

theorem CC19_equiv (G : Type*) [Magma G] : ConjunctionClass19 G <-> ConjunctionClass19_long G :=
Iff.intro (CC19_implies_long G) (CC19_implied_by_long G)

theorem CC20_implies_long (G : Type*) [Magma G] (h : ConjunctionClass20 G) : ConjunctionClass20_long G := by
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

theorem CC20_implied_by_long (G : Type*) [Magma G] : ConjunctionClass20_long G -> ConjunctionClass20 G :=
fun ⟨_, h43, h47, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h47, h4512⟩

theorem CC20_equiv (G : Type*) [Magma G] : ConjunctionClass20 G <-> ConjunctionClass20_long G :=
Iff.intro (CC20_implies_long G) (CC20_implied_by_long G)

theorem CC21_implies_long (G : Type*) [Magma G] (h : ConjunctionClass21 G) : ConjunctionClass21_long G := by
  obtain ⟨eq56, eq4512⟩ := h
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact ⟨eq1, eq47, eq56, eq4512⟩

theorem CC21_implied_by_long (G : Type*) [Magma G] : ConjunctionClass21_long G -> ConjunctionClass21 G :=
fun ⟨_, _, h56, h4512⟩ => ⟨h56, h4512⟩

theorem CC21_equiv (G : Type*) [Magma G] : ConjunctionClass21 G <-> ConjunctionClass21_long G :=
Iff.intro (CC21_implies_long G) (CC21_implied_by_long G)

theorem CC22_implies_long (G : Type*) [Magma G] (h : ConjunctionClass22 G) : ConjunctionClass22_long G := by
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

theorem CC22_implied_by_long (G : Type*) [Magma G] : ConjunctionClass22_long G -> ConjunctionClass22 G :=
fun ⟨_, h43, _, h56, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h56, h4512⟩

theorem CC22_equiv (G : Type*) [Magma G] : ConjunctionClass22 G <-> ConjunctionClass22_long G :=
Iff.intro (CC22_implies_long G) (CC22_implied_by_long G)

theorem CC23_implies_long (G : Type*) [Magma G] (h : ConjunctionClass23 G) : ConjunctionClass23_long G := by
  obtain ⟨eq75, eq4512⟩ := h
  have eq1 := Equation75_4512_implies_Equation1 G eq75 eq4512
  have eq47 := Equation75_4512_implies_Equation47 G eq75 eq4512
  exact ⟨eq1, eq47, eq75, eq4512⟩

theorem CC23_implied_by_long (G : Type*) [Magma G] : ConjunctionClass23_long G -> ConjunctionClass23 G :=
fun ⟨_, _, h75, h4512⟩ => ⟨h75, h4512⟩

theorem CC23_equiv (G : Type*) [Magma G] : ConjunctionClass23 G <-> ConjunctionClass23_long G :=
Iff.intro (CC23_implies_long G) (CC23_implied_by_long G)

theorem CC24_implies_long (G : Type*) [Magma G] (h : ConjunctionClass24 G) : ConjunctionClass24_long G := by
  obtain ⟨eq56, eq75, eq4512⟩ := h
  have eq4276 := Equation56_75_4512_implies_Equation4276 G eq56 eq75 eq4512
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact ⟨eq1, eq47, eq56, eq75, eq4276, eq4512⟩

theorem CC24_implied_by_long (G : Type*) [Magma G] : ConjunctionClass24_long G -> ConjunctionClass24 G :=
fun ⟨_, _, h56, h75, _, h4512⟩ => ⟨h56, h75, h4512⟩

theorem CC24_equiv (G : Type*) [Magma G] : ConjunctionClass24 G <-> ConjunctionClass24_long G :=
Iff.intro (CC24_implies_long G) (CC24_implied_by_long G)

theorem CC25_implies_long (G : Type*) [Magma G] (h : ConjunctionClass25 G) : ConjunctionClass25_long G := by
  obtain ⟨eq307, eq4512⟩ := h
  have eq1 := Equation307_4512_implies_Equation1 G eq307 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4512⟩

theorem CC25_implied_by_long (G : Type*) [Magma G] : ConjunctionClass25_long G -> ConjunctionClass25 G :=
fun ⟨_, h307, _, h4512⟩ => ⟨h307, h4512⟩

theorem CC25_equiv (G : Type*) [Magma G] : ConjunctionClass25 G <-> ConjunctionClass25_long G :=
Iff.intro (CC25_implies_long G) (CC25_implied_by_long G)

theorem CC26_implies_long (G : Type*) [Magma G] (h : ConjunctionClass26 G) : ConjunctionClass26_long G := by
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

theorem CC26_implied_by_long (G : Type*) [Magma G] : ConjunctionClass26_long G -> ConjunctionClass26 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h307, h4512⟩

theorem CC26_equiv (G : Type*) [Magma G] : ConjunctionClass26 G <-> ConjunctionClass26_long G :=
Iff.intro (CC26_implies_long G) (CC26_implied_by_long G)

theorem CC27_implies_long (G : Type*) [Magma G] (h : ConjunctionClass27 G) : ConjunctionClass27_long G := by
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

theorem CC27_implied_by_long (G : Type*) [Magma G] : ConjunctionClass27_long G -> ConjunctionClass27 G :=
fun ⟨_, h43, h307, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h307, h4512⟩

theorem CC27_equiv (G : Type*) [Magma G] : ConjunctionClass27 G <-> ConjunctionClass27_long G :=
Iff.intro (CC27_implies_long G) (CC27_implied_by_long G)

theorem CC28_implies_long (G : Type*) [Magma G] (h : ConjunctionClass28 G) : ConjunctionClass28_long G := by
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

theorem CC28_implied_by_long (G : Type*) [Magma G] : ConjunctionClass28_long G -> ConjunctionClass28 G :=
fun ⟨_, h40, h43, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h43, h307, h4512⟩

theorem CC28_equiv (G : Type*) [Magma G] : ConjunctionClass28 G <-> ConjunctionClass28_long G :=
Iff.intro (CC28_implies_long G) (CC28_implied_by_long G)

theorem CC29_implies_long (G : Type*) [Magma G] (h : ConjunctionClass29 G) : ConjunctionClass29_long G := by
  obtain ⟨eq308, eq4512⟩ := h
  have eq1 := Equation308_4512_implies_Equation1 G eq308 eq4512
  have eq307 := Equation308_4512_implies_Equation307 G eq308 eq4512
  have eq3253 := Equation308_4512_implies_Equation3253 G eq308 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  exact ⟨eq1, eq307, eq308, eq3253, eq3255, eq3256, eq4268, eq4512⟩

theorem CC29_implied_by_long (G : Type*) [Magma G] : ConjunctionClass29_long G -> ConjunctionClass29 G :=
fun ⟨_, _, h308, _, _, _, _, h4512⟩ => ⟨h308, h4512⟩

theorem CC29_equiv (G : Type*) [Magma G] : ConjunctionClass29 G <-> ConjunctionClass29_long G :=
Iff.intro (CC29_implies_long G) (CC29_implied_by_long G)

theorem CC30_implies_long (G : Type*) [Magma G] (h : ConjunctionClass30 G) : ConjunctionClass30_long G := by
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

theorem CC30_implied_by_long (G : Type*) [Magma G] : ConjunctionClass30_long G -> ConjunctionClass30 G :=
fun ⟨_, _, h309, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h4512⟩

theorem CC30_equiv (G : Type*) [Magma G] : ConjunctionClass30 G <-> ConjunctionClass30_long G :=
Iff.intro (CC30_implies_long G) (CC30_implied_by_long G)

theorem CC31_implies_long (G : Type*) [Magma G] (h : ConjunctionClass31 G) : ConjunctionClass31_long G := by
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

theorem CC31_implied_by_long (G : Type*) [Magma G] : ConjunctionClass31_long G -> ConjunctionClass31 G :=
fun ⟨_, h40, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h309, h4512⟩

theorem CC31_equiv (G : Type*) [Magma G] : ConjunctionClass31 G <-> ConjunctionClass31_long G :=
Iff.intro (CC31_implies_long G) (CC31_implied_by_long G)

theorem CC32_implies_long (G : Type*) [Magma G] (h : ConjunctionClass32 G) : ConjunctionClass32_long G := by
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

theorem CC32_implied_by_long (G : Type*) [Magma G] : ConjunctionClass32_long G -> ConjunctionClass32 G :=
fun ⟨_, _, h308, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h308, h309, h4512⟩

theorem CC32_equiv (G : Type*) [Magma G] : ConjunctionClass32 G <-> ConjunctionClass32_long G :=
Iff.intro (CC32_implies_long G) (CC32_implied_by_long G)

theorem CC33_implies_long (G : Type*) [Magma G] (h : ConjunctionClass33 G) : ConjunctionClass33_long G := by
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

theorem CC33_implied_by_long (G : Type*) [Magma G] : ConjunctionClass33_long G -> ConjunctionClass33 G :=
fun ⟨_, _, _, h310, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h310, h4512⟩

theorem CC33_equiv (G : Type*) [Magma G] : ConjunctionClass33 G <-> ConjunctionClass33_long G :=
Iff.intro (CC33_implies_long G) (CC33_implied_by_long G)

theorem CC34_implies_long (G : Type*) [Magma G] (h : ConjunctionClass34 G) : ConjunctionClass34_long G := by
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

theorem CC34_implied_by_long (G : Type*) [Magma G] : ConjunctionClass34_long G -> ConjunctionClass34 G :=
fun ⟨_, _, _, _, _, h311, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h311, h4512⟩

theorem CC34_equiv (G : Type*) [Magma G] : ConjunctionClass34 G <-> ConjunctionClass34_long G :=
Iff.intro (CC34_implies_long G) (CC34_implied_by_long G)

theorem CC35_implies_long (G : Type*) [Magma G] (h : ConjunctionClass35 G) : ConjunctionClass35_long G := by
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

theorem CC35_implied_by_long (G : Type*) [Magma G] : ConjunctionClass35_long G -> ConjunctionClass35 G :=
fun ⟨_, h40, _, _, _, _, h311, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h311, h4512⟩

theorem CC35_equiv (G : Type*) [Magma G] : ConjunctionClass35 G <-> ConjunctionClass35_long G :=
Iff.intro (CC35_implies_long G) (CC35_implied_by_long G)

theorem CC36_implies_long (G : Type*) [Magma G] (h : ConjunctionClass36 G) : ConjunctionClass36_long G := by
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

theorem CC36_implied_by_long (G : Type*) [Magma G] : ConjunctionClass36_long G -> ConjunctionClass36 G :=
fun ⟨_, _, h43, _, _, _, _, h311, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h311, h4512⟩

theorem CC36_equiv (G : Type*) [Magma G] : ConjunctionClass36 G <-> ConjunctionClass36_long G :=
Iff.intro (CC36_implies_long G) (CC36_implied_by_long G)

theorem CC37_implies_long (G : Type*) [Magma G] (h : ConjunctionClass37 G) : ConjunctionClass37_long G := by
  obtain ⟨eq312, eq4512⟩ := h
  have eq1 := Equation312_4512_implies_Equation1 G eq312 eq4512
  have eq307 := Equation312_4512_implies_Equation307 G eq312 eq4512
  have eq3253 := Equation312_4512_implies_Equation3253 G eq312 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  exact ⟨eq1, eq307, eq312, eq3253, eq3258, eq3278, eq4272, eq4512⟩

theorem CC37_implied_by_long (G : Type*) [Magma G] : ConjunctionClass37_long G -> ConjunctionClass37 G :=
fun ⟨_, _, h312, _, _, _, _, h4512⟩ => ⟨h312, h4512⟩

theorem CC37_equiv (G : Type*) [Magma G] : ConjunctionClass37 G <-> ConjunctionClass37_long G :=
Iff.intro (CC37_implies_long G) (CC37_implied_by_long G)

theorem CC38_implies_long (G : Type*) [Magma G] (h : ConjunctionClass38 G) : ConjunctionClass38_long G := by
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

theorem CC38_implied_by_long (G : Type*) [Magma G] : ConjunctionClass38_long G -> ConjunctionClass38 G :=
fun ⟨_, _, h309, h312, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h312, h4512⟩

theorem CC38_equiv (G : Type*) [Magma G] : ConjunctionClass38 G <-> ConjunctionClass38_long G :=
Iff.intro (CC38_implies_long G) (CC38_implied_by_long G)

theorem CC39_implies_long (G : Type*) [Magma G] (h : ConjunctionClass39 G) : ConjunctionClass39_long G := by
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

theorem CC39_implied_by_long (G : Type*) [Magma G] : ConjunctionClass39_long G -> ConjunctionClass39 G :=
fun ⟨_, _, _, h315, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h315, h4512⟩

theorem CC39_equiv (G : Type*) [Magma G] : ConjunctionClass39 G <-> ConjunctionClass39_long G :=
Iff.intro (CC39_implies_long G) (CC39_implied_by_long G)

theorem CC40_implies_long (G : Type*) [Magma G] (h : ConjunctionClass40 G) : ConjunctionClass40_long G := by
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

theorem CC40_implied_by_long (G : Type*) [Magma G] : ConjunctionClass40_long G -> ConjunctionClass40 G :=
fun ⟨_, _, _, _, _, h318, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h318, h4512⟩

theorem CC40_equiv (G : Type*) [Magma G] : ConjunctionClass40 G <-> ConjunctionClass40_long G :=
Iff.intro (CC40_implies_long G) (CC40_implied_by_long G)

theorem CC41_implies_long (G : Type*) [Magma G] (h : ConjunctionClass41 G) : ConjunctionClass41_long G := by
  obtain ⟨eq323, eq4512⟩ := h
  have eq1 := Equation323_4512_implies_Equation1 G eq323 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4512⟩

theorem CC41_implied_by_long (G : Type*) [Magma G] : ConjunctionClass41_long G -> ConjunctionClass41 G :=
fun ⟨_, _, h323, _, _, h4512⟩ => ⟨h323, h4512⟩

theorem CC41_equiv (G : Type*) [Magma G] : ConjunctionClass41 G <-> ConjunctionClass41_long G :=
Iff.intro (CC41_implies_long G) (CC41_implied_by_long G)

theorem CC42_implies_long (G : Type*) [Magma G] (h : ConjunctionClass42 G) : ConjunctionClass42_long G := by
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

theorem CC42_implied_by_long (G : Type*) [Magma G] : ConjunctionClass42_long G -> ConjunctionClass42 G :=
fun ⟨_, h43, _, h323, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h323, h4512⟩

theorem CC42_equiv (G : Type*) [Magma G] : ConjunctionClass42 G <-> ConjunctionClass42_long G :=
Iff.intro (CC42_implies_long G) (CC42_implied_by_long G)

theorem CC43_implies_long (G : Type*) [Magma G] (h : ConjunctionClass43 G) : ConjunctionClass43_long G := by
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

theorem CC43_implied_by_long (G : Type*) [Magma G] : ConjunctionClass43_long G -> ConjunctionClass43 G :=
fun ⟨_, _, h309, h323, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h323, h4512⟩

theorem CC43_equiv (G : Type*) [Magma G] : ConjunctionClass43 G <-> ConjunctionClass43_long G :=
Iff.intro (CC43_implies_long G) (CC43_implied_by_long G)

theorem CC44_implies_long (G : Type*) [Magma G] (h : ConjunctionClass44 G) : ConjunctionClass44_long G := by
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

theorem CC44_implied_by_long (G : Type*) [Magma G] : ConjunctionClass44_long G -> ConjunctionClass44 G :=
fun ⟨_, _, h312, h323, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h312, h323, h4512⟩

theorem CC44_equiv (G : Type*) [Magma G] : ConjunctionClass44 G <-> ConjunctionClass44_long G :=
Iff.intro (CC44_implies_long G) (CC44_implied_by_long G)

theorem CC45_implies_long (G : Type*) [Magma G] (h : ConjunctionClass45 G) : ConjunctionClass45_long G := by
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

theorem CC45_implied_by_long (G : Type*) [Magma G] : ConjunctionClass45_long G -> ConjunctionClass45 G :=
fun ⟨_, _, h325, _, _, _, _, _, _, h4512⟩ => ⟨h325, h4512⟩

theorem CC45_equiv (G : Type*) [Magma G] : ConjunctionClass45 G <-> ConjunctionClass45_long G :=
Iff.intro (CC45_implies_long G) (CC45_implied_by_long G)

theorem CC46_implies_long (G : Type*) [Magma G] (h : ConjunctionClass46 G) : ConjunctionClass46_long G := by
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

theorem CC46_implied_by_long (G : Type*) [Magma G] : ConjunctionClass46_long G -> ConjunctionClass46 G :=
fun ⟨_, h3, _, _, _, _, h325, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h325, h4512⟩

theorem CC46_equiv (G : Type*) [Magma G] : ConjunctionClass46 G <-> ConjunctionClass46_long G :=
Iff.intro (CC46_implies_long G) (CC46_implied_by_long G)

theorem CC47_implies_long (G : Type*) [Magma G] (h : ConjunctionClass47 G) : ConjunctionClass47_long G := by
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

theorem CC47_implied_by_long (G : Type*) [Magma G] : ConjunctionClass47_long G -> ConjunctionClass47 G :=
fun ⟨_, _, h308, h325, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h308, h325, h4512⟩

theorem CC47_equiv (G : Type*) [Magma G] : ConjunctionClass47 G <-> ConjunctionClass47_long G :=
Iff.intro (CC47_implies_long G) (CC47_implied_by_long G)

theorem CC48_implies_long (G : Type*) [Magma G] (h : ConjunctionClass48 G) : ConjunctionClass48_long G := by
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

theorem CC48_implied_by_long (G : Type*) [Magma G] : ConjunctionClass48_long G -> ConjunctionClass48 G :=
fun ⟨_, _, h323, h325, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h323, h325, h4512⟩

theorem CC48_equiv (G : Type*) [Magma G] : ConjunctionClass48 G <-> ConjunctionClass48_long G :=
Iff.intro (CC48_implies_long G) (CC48_implied_by_long G)

theorem CC49_implies_long (G : Type*) [Magma G] (h : ConjunctionClass49 G) : ConjunctionClass49_long G := by
  obtain ⟨eq326, eq4512⟩ := h
  have eq1 := Equation326_4512_implies_Equation1 G eq326 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4512⟩

theorem CC49_implied_by_long (G : Type*) [Magma G] : ConjunctionClass49_long G -> ConjunctionClass49 G :=
fun ⟨_, _, h326, _, _, h4512⟩ => ⟨h326, h4512⟩

theorem CC49_equiv (G : Type*) [Magma G] : ConjunctionClass49 G <-> ConjunctionClass49_long G :=
Iff.intro (CC49_implies_long G) (CC49_implied_by_long G)

theorem CC50_implies_long (G : Type*) [Magma G] (h : ConjunctionClass50 G) : ConjunctionClass50_long G := by
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

theorem CC50_implied_by_long (G : Type*) [Magma G] : ConjunctionClass50_long G -> ConjunctionClass50 G :=
fun ⟨_, _, h323, h326, _, _, _, _, _, _, h4512⟩ => ⟨h323, h326, h4512⟩

theorem CC50_equiv (G : Type*) [Magma G] : ConjunctionClass50 G <-> ConjunctionClass50_long G :=
Iff.intro (CC50_implies_long G) (CC50_implied_by_long G)

theorem CC51_implies_long (G : Type*) [Magma G] (h : ConjunctionClass51 G) : ConjunctionClass51_long G := by
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

theorem CC51_implied_by_long (G : Type*) [Magma G] : ConjunctionClass51_long G -> ConjunctionClass51 G :=
fun ⟨_, _, _, h333, _, _, _, _, _, h4512⟩ => ⟨h333, h4512⟩

theorem CC51_equiv (G : Type*) [Magma G] : ConjunctionClass51 G <-> ConjunctionClass51_long G :=
Iff.intro (CC51_implies_long G) (CC51_implied_by_long G)

theorem CC52_implies_long (G : Type*) [Magma G] (h : ConjunctionClass52 G) : ConjunctionClass52_long G := by
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

theorem CC52_implied_by_long (G : Type*) [Magma G] : ConjunctionClass52_long G -> ConjunctionClass52 G :=
fun ⟨_, h3, _, _, _, _, _, h333, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3, h333, h4512⟩

theorem CC52_equiv (G : Type*) [Magma G] : ConjunctionClass52 G <-> ConjunctionClass52_long G :=
Iff.intro (CC52_implies_long G) (CC52_implied_by_long G)

theorem CC53_implies_long (G : Type*) [Magma G] (h : ConjunctionClass53 G) : ConjunctionClass53_long G := by
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

theorem CC53_implied_by_long (G : Type*) [Magma G] : ConjunctionClass53_long G -> ConjunctionClass53 G :=
fun ⟨_, _, _, h326, h333, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h326, h333, h4512⟩

theorem CC53_equiv (G : Type*) [Magma G] : ConjunctionClass53 G <-> ConjunctionClass53_long G :=
Iff.intro (CC53_implies_long G) (CC53_implied_by_long G)

theorem CC54_implies_long (G : Type*) [Magma G] (h : ConjunctionClass54 G) : ConjunctionClass54_long G := by
  obtain ⟨eq411, eq4512⟩ := h
  have eq1 := Equation411_4512_implies_Equation1 G eq411 eq4512
  exact ⟨eq1, eq411, eq4512⟩

theorem CC54_implied_by_long (G : Type*) [Magma G] : ConjunctionClass54_long G -> ConjunctionClass54 G :=
fun ⟨_, h411, h4512⟩ => ⟨h411, h4512⟩

theorem CC54_equiv (G : Type*) [Magma G] : ConjunctionClass54 G <-> ConjunctionClass54_long G :=
Iff.intro (CC54_implies_long G) (CC54_implied_by_long G)

theorem CC55_implies_long (G : Type*) [Magma G] (h : ConjunctionClass55 G) : ConjunctionClass55_long G := by
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

theorem CC55_implied_by_long (G : Type*) [Magma G] : ConjunctionClass55_long G -> ConjunctionClass55 G :=
fun ⟨_, h43, h411, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h411, h4512⟩

theorem CC55_equiv (G : Type*) [Magma G] : ConjunctionClass55 G <-> ConjunctionClass55_long G :=
Iff.intro (CC55_implies_long G) (CC55_implied_by_long G)

theorem CC56_implies_long (G : Type*) [Magma G] (h : ConjunctionClass56 G) : ConjunctionClass56_long G := by
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

theorem CC56_implied_by_long (G : Type*) [Magma G] : ConjunctionClass56_long G -> ConjunctionClass56 G :=
fun ⟨_, _, _, h419, _, _, _, _, _, _, h4512⟩ => ⟨h419, h4512⟩

theorem CC56_equiv (G : Type*) [Magma G] : ConjunctionClass56 G <-> ConjunctionClass56_long G :=
Iff.intro (CC56_implies_long G) (CC56_implied_by_long G)

theorem CC57_implies_long (G : Type*) [Magma G] (h : ConjunctionClass57 G) : ConjunctionClass57_long G := by
  obtain ⟨eq429, eq4512⟩ := h
  have eq1 := Equation429_4512_implies_Equation1 G eq429 eq4512
  have eq8 := Equation429_4512_implies_Equation8 G eq429 eq4512
  have eq411 := Equation429_4512_implies_Equation411 G eq429 eq4512
  have eq3253 := Equation429_4512_implies_Equation3253 G eq429 eq4512
  have eq3306 := Equation429_4512_implies_Equation3306 G eq429 eq4512
  have eq3319 := Equation429_4512_implies_Equation3319 G eq429 eq4512
  exact ⟨eq1, eq8, eq411, eq429, eq3253, eq3306, eq3319, eq4512⟩

theorem CC57_implied_by_long (G : Type*) [Magma G] : ConjunctionClass57_long G -> ConjunctionClass57 G :=
fun ⟨_, _, _, h429, _, _, _, h4512⟩ => ⟨h429, h4512⟩

theorem CC57_equiv (G : Type*) [Magma G] : ConjunctionClass57 G <-> ConjunctionClass57_long G :=
Iff.intro (CC57_implies_long G) (CC57_implied_by_long G)

theorem CC58_implies_long (G : Type*) [Magma G] (h : ConjunctionClass58 G) : ConjunctionClass58_long G := by
  obtain ⟨eq440, eq4512⟩ := h
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact ⟨eq1, eq411, eq440, eq4512⟩

theorem CC58_implied_by_long (G : Type*) [Magma G] : ConjunctionClass58_long G -> ConjunctionClass58 G :=
fun ⟨_, _, h440, h4512⟩ => ⟨h440, h4512⟩

theorem CC58_equiv (G : Type*) [Magma G] : ConjunctionClass58 G <-> ConjunctionClass58_long G :=
Iff.intro (CC58_implies_long G) (CC58_implied_by_long G)

theorem CC59_implies_long (G : Type*) [Magma G] (h : ConjunctionClass59 G) : ConjunctionClass59_long G := by
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

theorem CC59_implied_by_long (G : Type*) [Magma G] : ConjunctionClass59_long G -> ConjunctionClass59 G :=
fun ⟨_, h43, _, h440, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h440, h4512⟩

theorem CC59_equiv (G : Type*) [Magma G] : ConjunctionClass59 G <-> ConjunctionClass59_long G :=
Iff.intro (CC59_implies_long G) (CC59_implied_by_long G)

theorem CC60_implies_long (G : Type*) [Magma G] (h : ConjunctionClass60 G) : ConjunctionClass60_long G := by
  obtain ⟨eq504, eq4512⟩ := h
  have eq1 := Equation504_4512_implies_Equation1 G eq504 eq4512
  have eq411 := Equation504_4512_implies_Equation411 G eq504 eq4512
  have eq440 := Equation504_4512_implies_Equation440 G eq504 eq4512
  have eq513 := Equation504_4512_implies_Equation513 G eq504 eq4512
  have eq4290 := Equation504_4512_implies_Equation4290 G eq504 eq4512
  exact ⟨eq1, eq411, eq440, eq504, eq513, eq4290, eq4512⟩

theorem CC60_implied_by_long (G : Type*) [Magma G] : ConjunctionClass60_long G -> ConjunctionClass60 G :=
fun ⟨_, _, _, h504, _, _, h4512⟩ => ⟨h504, h4512⟩

theorem CC60_equiv (G : Type*) [Magma G] : ConjunctionClass60 G <-> ConjunctionClass60_long G :=
Iff.intro (CC60_implies_long G) (CC60_implied_by_long G)

theorem CC61_implies_long (G : Type*) [Magma G] (h : ConjunctionClass61 G) : ConjunctionClass61_long G := by
  obtain ⟨eq513, eq4512⟩ := h
  have eq1 := Equation513_4512_implies_Equation1 G eq513 eq4512
  have eq411 := Equation513_4512_implies_Equation411 G eq513 eq4512
  exact ⟨eq1, eq411, eq513, eq4512⟩

theorem CC61_implied_by_long (G : Type*) [Magma G] : ConjunctionClass61_long G -> ConjunctionClass61 G :=
fun ⟨_, _, h513, h4512⟩ => ⟨h513, h4512⟩

theorem CC61_equiv (G : Type*) [Magma G] : ConjunctionClass61 G <-> ConjunctionClass61_long G :=
Iff.intro (CC61_implies_long G) (CC61_implied_by_long G)

theorem CC62_implies_long (G : Type*) [Magma G] (h : ConjunctionClass62 G) : ConjunctionClass62_long G := by
  obtain ⟨eq440, eq513, eq4512⟩ := h
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact ⟨eq1, eq411, eq440, eq513, eq4512⟩

theorem CC62_implied_by_long (G : Type*) [Magma G] : ConjunctionClass62_long G -> ConjunctionClass62 G :=
fun ⟨_, _, h440, h513, h4512⟩ => ⟨h440, h513, h4512⟩

theorem CC62_equiv (G : Type*) [Magma G] : ConjunctionClass62 G <-> ConjunctionClass62_long G :=
Iff.intro (CC62_implies_long G) (CC62_implied_by_long G)

theorem CC63_implies_long (G : Type*) [Magma G] (h : ConjunctionClass63 G) : ConjunctionClass63_long G := by
  obtain ⟨eq3253, eq4512⟩ := h
  have eq1 := Equation3253_4512_implies_Equation1 G eq3253 eq4512
  exact ⟨eq1, eq3253, eq4512⟩

theorem CC63_implied_by_long (G : Type*) [Magma G] : ConjunctionClass63_long G -> ConjunctionClass63 G :=
fun ⟨_, h3253, h4512⟩ => ⟨h3253, h4512⟩

theorem CC63_equiv (G : Type*) [Magma G] : ConjunctionClass63 G <-> ConjunctionClass63_long G :=
Iff.intro (CC63_implies_long G) (CC63_implied_by_long G)

theorem CC64_implies_long (G : Type*) [Magma G] (h : ConjunctionClass64 G) : ConjunctionClass64_long G := by
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

theorem CC64_implied_by_long (G : Type*) [Magma G] : ConjunctionClass64_long G -> ConjunctionClass64 G :=
fun ⟨_, h43, h3253, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h3253, h4512⟩

theorem CC64_equiv (G : Type*) [Magma G] : ConjunctionClass64 G <-> ConjunctionClass64_long G :=
Iff.intro (CC64_implies_long G) (CC64_implied_by_long G)

theorem CC65_implies_long (G : Type*) [Magma G] (h : ConjunctionClass65 G) : ConjunctionClass65_long G := by
  obtain ⟨eq3255, eq4512⟩ := h
  have eq1 := Equation3255_4512_implies_Equation1 G eq3255 eq4512
  have eq307 := Equation3255_4512_implies_Equation307 G eq3255 eq4512
  have eq3253 := Equation3255_4512_implies_Equation3253 G eq3255 eq4512
  exact ⟨eq1, eq307, eq3253, eq3255, eq4512⟩

theorem CC65_implied_by_long (G : Type*) [Magma G] : ConjunctionClass65_long G -> ConjunctionClass65 G :=
fun ⟨_, _, _, h3255, h4512⟩ => ⟨h3255, h4512⟩

theorem CC65_equiv (G : Type*) [Magma G] : ConjunctionClass65 G <-> ConjunctionClass65_long G :=
Iff.intro (CC65_implies_long G) (CC65_implied_by_long G)

theorem CC66_implies_long (G : Type*) [Magma G] (h : ConjunctionClass66 G) : ConjunctionClass66_long G := by
  obtain ⟨eq326, eq3255, eq4512⟩ := h
  have eq3322 := Equation326_3255_4512_implies_Equation3322 G eq326 eq3255 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3322_4512_implies_Equation307 G eq3322 eq4512
  have eq3253 := Equation3322_4512_implies_Equation3253 G eq3322 eq4512
  have eq3316 := Equation3322_4512_implies_Equation3316 G eq3322 eq4512
  have eq3319 := Equation3322_4512_implies_Equation3319 G eq3322 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3255, eq3316, eq3319, eq3322, eq4512⟩

theorem CC66_implied_by_long (G : Type*) [Magma G] : ConjunctionClass66_long G -> ConjunctionClass66 G :=
fun ⟨_, _, h326, _, h3255, _, _, _, h4512⟩ => ⟨h326, h3255, h4512⟩

theorem CC66_equiv (G : Type*) [Magma G] : ConjunctionClass66 G <-> ConjunctionClass66_long G :=
Iff.intro (CC66_implies_long G) (CC66_implied_by_long G)

theorem CC67_implies_long (G : Type*) [Magma G] (h : ConjunctionClass67 G) : ConjunctionClass67_long G := by
  obtain ⟨eq3256, eq4512⟩ := h
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  exact ⟨eq1, eq3253, eq3256, eq4512⟩

theorem CC67_implied_by_long (G : Type*) [Magma G] : ConjunctionClass67_long G -> ConjunctionClass67 G :=
fun ⟨_, _, h3256, h4512⟩ => ⟨h3256, h4512⟩

theorem CC67_equiv (G : Type*) [Magma G] : ConjunctionClass67 G <-> ConjunctionClass67_long G :=
Iff.intro (CC67_implies_long G) (CC67_implied_by_long G)

theorem CC68_implies_long (G : Type*) [Magma G] (h : ConjunctionClass68 G) : ConjunctionClass68_long G := by
  obtain ⟨eq3258, eq4512⟩ := h
  have eq1 := Equation3258_4512_implies_Equation1 G eq3258 eq4512
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation3258_4512_implies_Equation3253 G eq3258 eq4512
  exact ⟨eq1, eq307, eq3253, eq3258, eq4512⟩

theorem CC68_implied_by_long (G : Type*) [Magma G] : ConjunctionClass68_long G -> ConjunctionClass68 G :=
fun ⟨_, _, _, h3258, h4512⟩ => ⟨h3258, h4512⟩

theorem CC68_equiv (G : Type*) [Magma G] : ConjunctionClass68 G <-> ConjunctionClass68_long G :=
Iff.intro (CC68_implies_long G) (CC68_implied_by_long G)

theorem CC69_implies_long (G : Type*) [Magma G] (h : ConjunctionClass69 G) : ConjunctionClass69_long G := by
  obtain ⟨eq323, eq3258, eq4512⟩ := h
  have eq3326 := Equation323_3258_4512_implies_Equation3326 G eq323 eq3258 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation3258_4512_implies_Equation3253 G eq3258 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq3316 := Equation3326_4512_implies_Equation3316 G eq3326 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3258, eq3306, eq3316, eq3326, eq4512⟩

theorem CC69_implied_by_long (G : Type*) [Magma G] : ConjunctionClass69_long G -> ConjunctionClass69 G :=
fun ⟨_, _, h323, _, h3258, _, _, _, h4512⟩ => ⟨h323, h3258, h4512⟩

theorem CC69_equiv (G : Type*) [Magma G] : ConjunctionClass69 G <-> ConjunctionClass69_long G :=
Iff.intro (CC69_implies_long G) (CC69_implied_by_long G)

theorem CC70_implies_long (G : Type*) [Magma G] (h : ConjunctionClass70 G) : ConjunctionClass70_long G := by
  obtain ⟨eq3255, eq3258, eq4512⟩ := h
  have eq3261 := Equation3255_3258_4512_implies_Equation3261 G eq3255 eq3258 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3258_4512_implies_Equation307 G eq3258 eq4512
  have eq3253 := Equation3258_4512_implies_Equation3253 G eq3258 eq4512
  have eq4284 := Equation307_3261_4512_implies_Equation4284 G eq307 eq3261 eq4512
  exact ⟨eq1, eq307, eq3253, eq3255, eq3258, eq3261, eq4284, eq4512⟩

theorem CC70_implied_by_long (G : Type*) [Magma G] : ConjunctionClass70_long G -> ConjunctionClass70 G :=
fun ⟨_, _, _, h3255, h3258, _, _, h4512⟩ => ⟨h3255, h3258, h4512⟩

theorem CC70_equiv (G : Type*) [Magma G] : ConjunctionClass70 G <-> ConjunctionClass70_long G :=
Iff.intro (CC70_implies_long G) (CC70_implied_by_long G)

theorem CC71_implies_long (G : Type*) [Magma G] (h : ConjunctionClass71 G) : ConjunctionClass71_long G := by
  obtain ⟨eq3259, eq4512⟩ := h
  have eq1 := Equation3259_4512_implies_Equation1 G eq3259 eq4512
  have eq3253 := Equation3259_4512_implies_Equation3253 G eq3259 eq4512
  have eq3256 := Equation3259_4512_implies_Equation3256 G eq3259 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq4270, eq4512⟩

theorem CC71_implied_by_long (G : Type*) [Magma G] : ConjunctionClass71_long G -> ConjunctionClass71 G :=
fun ⟨_, _, _, h3259, _, _, h4512⟩ => ⟨h3259, h4512⟩

theorem CC71_equiv (G : Type*) [Magma G] : ConjunctionClass71 G <-> ConjunctionClass71_long G :=
Iff.intro (CC71_implies_long G) (CC71_implied_by_long G)

theorem CC72_implies_long (G : Type*) [Magma G] (h : ConjunctionClass72 G) : ConjunctionClass72_long G := by
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

theorem CC72_implied_by_long (G : Type*) [Magma G] : ConjunctionClass72_long G -> ConjunctionClass72 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, _, _, _, _, h4512⟩ => ⟨h3260, h4512⟩

theorem CC72_equiv (G : Type*) [Magma G] : ConjunctionClass72 G <-> ConjunctionClass72_long G :=
Iff.intro (CC72_implies_long G) (CC72_implied_by_long G)

theorem CC73_implies_long (G : Type*) [Magma G] (h : ConjunctionClass73 G) : ConjunctionClass73_long G := by
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

theorem CC73_implied_by_long (G : Type*) [Magma G] : ConjunctionClass73_long G -> ConjunctionClass73 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h4512⟩

theorem CC73_equiv (G : Type*) [Magma G] : ConjunctionClass73 G <-> ConjunctionClass73_long G :=
Iff.intro (CC73_implies_long G) (CC73_implied_by_long G)

theorem CC74_implies_long (G : Type*) [Magma G] (h : ConjunctionClass74 G) : ConjunctionClass74_long G := by
  obtain ⟨eq3261, eq4512⟩ := h
  have eq1 := Equation3261_4512_implies_Equation1 G eq3261 eq4512
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  exact ⟨eq1, eq3253, eq3261, eq4512⟩

theorem CC74_implied_by_long (G : Type*) [Magma G] : ConjunctionClass74_long G -> ConjunctionClass74 G :=
fun ⟨_, _, h3261, h4512⟩ => ⟨h3261, h4512⟩

theorem CC74_equiv (G : Type*) [Magma G] : ConjunctionClass74 G <-> ConjunctionClass74_long G :=
Iff.intro (CC74_implies_long G) (CC74_implied_by_long G)

theorem CC75_implies_long (G : Type*) [Magma G] (h : ConjunctionClass75 G) : ConjunctionClass75_long G := by
  obtain ⟨eq3264, eq4512⟩ := h
  have eq1 := Equation3264_4512_implies_Equation1 G eq3264 eq4512
  have eq307 := Equation3264_4512_implies_Equation307 G eq3264 eq4512
  have eq3253 := Equation3264_4512_implies_Equation3253 G eq3264 eq4512
  have eq3255 := Equation3264_4512_implies_Equation3255 G eq3264 eq4512
  have eq3258 := Equation3264_4512_implies_Equation3258 G eq3264 eq4512
  have eq3261 := Equation3264_4512_implies_Equation3261 G eq3264 eq4512
  have eq4284 := Equation3264_4512_implies_Equation4284 G eq3264 eq4512
  exact ⟨eq1, eq307, eq3253, eq3255, eq3258, eq3261, eq3264, eq4284, eq4512⟩

theorem CC75_implied_by_long (G : Type*) [Magma G] : ConjunctionClass75_long G -> ConjunctionClass75 G :=
fun ⟨_, _, _, _, _, _, h3264, _, h4512⟩ => ⟨h3264, h4512⟩

theorem CC75_equiv (G : Type*) [Magma G] : ConjunctionClass75 G <-> ConjunctionClass75_long G :=
Iff.intro (CC75_implies_long G) (CC75_implied_by_long G)

theorem CC76_implies_long (G : Type*) [Magma G] (h : ConjunctionClass76 G) : ConjunctionClass76_long G := by
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

theorem CC76_implied_by_long (G : Type*) [Magma G] : ConjunctionClass76_long G -> ConjunctionClass76 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, h3264, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3264, h4512⟩

theorem CC76_equiv (G : Type*) [Magma G] : ConjunctionClass76 G <-> ConjunctionClass76_long G :=
Iff.intro (CC76_implies_long G) (CC76_implied_by_long G)

theorem CC77_implies_long (G : Type*) [Magma G] (h : ConjunctionClass77 G) : ConjunctionClass77_long G := by
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

theorem CC77_implied_by_long (G : Type*) [Magma G] : ConjunctionClass77_long G -> ConjunctionClass77 G :=
fun ⟨_, _, h308, _, _, _, _, _, _, _, h3264, _, _, _, _, h4512⟩ => ⟨h308, h3264, h4512⟩

theorem CC77_equiv (G : Type*) [Magma G] : ConjunctionClass77 G <-> ConjunctionClass77_long G :=
Iff.intro (CC77_implies_long G) (CC77_implied_by_long G)

theorem CC78_implies_long (G : Type*) [Magma G] (h : ConjunctionClass78 G) : ConjunctionClass78_long G := by
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

theorem CC78_implied_by_long (G : Type*) [Magma G] : ConjunctionClass78_long G -> ConjunctionClass78 G :=
fun ⟨_, _, h312, _, _, _, _, _, h3264, _, _, _, _, _, _, h4512⟩ => ⟨h312, h3264, h4512⟩

theorem CC78_equiv (G : Type*) [Magma G] : ConjunctionClass78 G <-> ConjunctionClass78_long G :=
Iff.intro (CC78_implies_long G) (CC78_implied_by_long G)

theorem CC79_implies_long (G : Type*) [Magma G] (h : ConjunctionClass79 G) : ConjunctionClass79_long G := by
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

theorem CC79_implied_by_long (G : Type*) [Magma G] : ConjunctionClass79_long G -> ConjunctionClass79 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, h3264, _, _, _, _, h4512⟩ => ⟨h3260, h3264, h4512⟩

theorem CC79_equiv (G : Type*) [Magma G] : ConjunctionClass79 G <-> ConjunctionClass79_long G :=
Iff.intro (CC79_implies_long G) (CC79_implied_by_long G)

theorem CC80_implies_long (G : Type*) [Magma G] (h : ConjunctionClass80 G) : ConjunctionClass80_long G := by
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

theorem CC80_implied_by_long (G : Type*) [Magma G] : ConjunctionClass80_long G -> ConjunctionClass80 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, h3264, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h3264, h4512⟩

theorem CC80_equiv (G : Type*) [Magma G] : ConjunctionClass80 G <-> ConjunctionClass80_long G :=
Iff.intro (CC80_implies_long G) (CC80_implied_by_long G)

theorem CC81_implies_long (G : Type*) [Magma G] (h : ConjunctionClass81 G) : ConjunctionClass81_long G := by
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

theorem CC81_implied_by_long (G : Type*) [Magma G] : ConjunctionClass81_long G -> ConjunctionClass81 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, h3265, _, _, _, _, h4512⟩ => ⟨h3265, h4512⟩

theorem CC81_equiv (G : Type*) [Magma G] : ConjunctionClass81 G <-> ConjunctionClass81_long G :=
Iff.intro (CC81_implies_long G) (CC81_implied_by_long G)

theorem CC82_implies_long (G : Type*) [Magma G] (h : ConjunctionClass82 G) : ConjunctionClass82_long G := by
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

theorem CC82_implied_by_long (G : Type*) [Magma G] : ConjunctionClass82_long G -> ConjunctionClass82 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3265, h4512⟩

theorem CC82_equiv (G : Type*) [Magma G] : ConjunctionClass82 G <-> ConjunctionClass82_long G :=
Iff.intro (CC82_implies_long G) (CC82_implied_by_long G)

theorem CC83_implies_long (G : Type*) [Magma G] (h : ConjunctionClass83 G) : ConjunctionClass83_long G := by
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

theorem CC83_implied_by_long (G : Type*) [Magma G] : ConjunctionClass83_long G -> ConjunctionClass83 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, h3265, _, _, _, _, h4512⟩ => ⟨h3260, h3265, h4512⟩

theorem CC83_equiv (G : Type*) [Magma G] : ConjunctionClass83 G <-> ConjunctionClass83_long G :=
Iff.intro (CC83_implies_long G) (CC83_implied_by_long G)

theorem CC84_implies_long (G : Type*) [Magma G] (h : ConjunctionClass84 G) : ConjunctionClass84_long G := by
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

theorem CC84_implied_by_long (G : Type*) [Magma G] : ConjunctionClass84_long G -> ConjunctionClass84 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h3265, h4512⟩

theorem CC84_equiv (G : Type*) [Magma G] : ConjunctionClass84 G <-> ConjunctionClass84_long G :=
Iff.intro (CC84_implies_long G) (CC84_implied_by_long G)

theorem CC85_implies_long (G : Type*) [Magma G] (h : ConjunctionClass85 G) : ConjunctionClass85_long G := by
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

theorem CC85_implied_by_long (G : Type*) [Magma G] : ConjunctionClass85_long G -> ConjunctionClass85 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, h3264, h3265, _, _, _, _, h4512⟩ => ⟨h3264, h3265, h4512⟩

theorem CC85_equiv (G : Type*) [Magma G] : ConjunctionClass85 G <-> ConjunctionClass85_long G :=
Iff.intro (CC85_implies_long G) (CC85_implied_by_long G)

theorem CC86_implies_long (G : Type*) [Magma G] (h : ConjunctionClass86 G) : ConjunctionClass86_long G := by
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

theorem CC86_implied_by_long (G : Type*) [Magma G] : ConjunctionClass86_long G -> ConjunctionClass86 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, h3264, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3264, h3265, h4512⟩

theorem CC86_equiv (G : Type*) [Magma G] : ConjunctionClass86 G <-> ConjunctionClass86_long G :=
Iff.intro (CC86_implies_long G) (CC86_implied_by_long G)

theorem CC87_implies_long (G : Type*) [Magma G] (h : ConjunctionClass87 G) : ConjunctionClass87_long G := by
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

theorem CC87_implied_by_long (G : Type*) [Magma G] : ConjunctionClass87_long G -> ConjunctionClass87 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3260, _, h3264, h3265, _, _, _, _, h4512⟩ => ⟨h3260, h3264, h3265, h4512⟩

theorem CC87_equiv (G : Type*) [Magma G] : ConjunctionClass87 G <-> ConjunctionClass87_long G :=
Iff.intro (CC87_implies_long G) (CC87_implied_by_long G)

theorem CC88_implies_long (G : Type*) [Magma G] (h : ConjunctionClass88 G) : ConjunctionClass88_long G := by
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

theorem CC88_implied_by_long (G : Type*) [Magma G] : ConjunctionClass88_long G -> ConjunctionClass88 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, h3260, _, h3264, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3260, h3264, h3265, h4512⟩

theorem CC88_equiv (G : Type*) [Magma G] : ConjunctionClass88 G <-> ConjunctionClass88_long G :=
Iff.intro (CC88_implies_long G) (CC88_implied_by_long G)

theorem CC89_implies_long (G : Type*) [Magma G] (h : ConjunctionClass89 G) : ConjunctionClass89_long G := by
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

theorem CC89_implied_by_long (G : Type*) [Magma G] : ConjunctionClass89_long G -> ConjunctionClass89 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, h4512⟩ => ⟨h3267, h4512⟩

theorem CC89_equiv (G : Type*) [Magma G] : ConjunctionClass89 G <-> ConjunctionClass89_long G :=
Iff.intro (CC89_implies_long G) (CC89_implied_by_long G)

theorem CC90_implies_long (G : Type*) [Magma G] (h : ConjunctionClass90 G) : ConjunctionClass90_long G := by
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

theorem CC90_implied_by_long (G : Type*) [Magma G] : ConjunctionClass90_long G -> ConjunctionClass90 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3267, h4512⟩

theorem CC90_equiv (G : Type*) [Magma G] : ConjunctionClass90 G <-> ConjunctionClass90_long G :=
Iff.intro (CC90_implies_long G) (CC90_implied_by_long G)

theorem CC91_implies_long (G : Type*) [Magma G] (h : ConjunctionClass91 G) : ConjunctionClass91_long G := by
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

theorem CC91_implied_by_long (G : Type*) [Magma G] : ConjunctionClass91_long G -> ConjunctionClass91 G :=
fun ⟨_, _, h43, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h3267, h4512⟩

theorem CC91_equiv (G : Type*) [Magma G] : ConjunctionClass91 G <-> ConjunctionClass91_long G :=
Iff.intro (CC91_implies_long G) (CC91_implied_by_long G)

theorem CC92_implies_long (G : Type*) [Magma G] (h : ConjunctionClass92 G) : ConjunctionClass92_long G := by
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

theorem CC92_implied_by_long (G : Type*) [Magma G] : ConjunctionClass92_long G -> ConjunctionClass92 G :=
fun ⟨_, _, _, h309, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h3267, h4512⟩

theorem CC92_equiv (G : Type*) [Magma G] : ConjunctionClass92 G <-> ConjunctionClass92_long G :=
Iff.intro (CC92_implies_long G) (CC92_implied_by_long G)

theorem CC93_implies_long (G : Type*) [Magma G] (h : ConjunctionClass93 G) : ConjunctionClass93_long G := by
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

theorem CC93_implied_by_long (G : Type*) [Magma G] : ConjunctionClass93_long G -> ConjunctionClass93 G :=
fun ⟨_, h40, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h309, h3267, h4512⟩

theorem CC93_equiv (G : Type*) [Magma G] : ConjunctionClass93 G <-> ConjunctionClass93_long G :=
Iff.intro (CC93_implies_long G) (CC93_implied_by_long G)

theorem CC94_implies_long (G : Type*) [Magma G] (h : ConjunctionClass94 G) : ConjunctionClass94_long G := by
  obtain ⟨eq3271, eq4512⟩ := h
  have eq1 := Equation3271_4512_implies_Equation1 G eq3271 eq4512
  have eq3253 := Equation3271_4512_implies_Equation3253 G eq3271 eq4512
  have eq3261 := Equation3271_4512_implies_Equation3261 G eq3271 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq4275, eq4512⟩

theorem CC94_implied_by_long (G : Type*) [Magma G] : ConjunctionClass94_long G -> ConjunctionClass94 G :=
fun ⟨_, _, _, h3271, _, _, h4512⟩ => ⟨h3271, h4512⟩

theorem CC94_equiv (G : Type*) [Magma G] : ConjunctionClass94 G <-> ConjunctionClass94_long G :=
Iff.intro (CC94_implies_long G) (CC94_implied_by_long G)

theorem CC95_implies_long (G : Type*) [Magma G] (h : ConjunctionClass95 G) : ConjunctionClass95_long G := by
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

theorem CC95_implied_by_long (G : Type*) [Magma G] : ConjunctionClass95_long G -> ConjunctionClass95 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3274, _, _, _, _, _, h4512⟩ => ⟨h3274, h4512⟩

theorem CC95_equiv (G : Type*) [Magma G] : ConjunctionClass95 G <-> ConjunctionClass95_long G :=
Iff.intro (CC95_implies_long G) (CC95_implied_by_long G)

theorem CC96_implies_long (G : Type*) [Magma G] (h : ConjunctionClass96 G) : ConjunctionClass96_long G := by
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

theorem CC96_implied_by_long (G : Type*) [Magma G] : ConjunctionClass96_long G -> ConjunctionClass96 G :=
fun ⟨_, _, _, _, _, _, _, _, h3264, _, h3274, _, _, _, _, _, h4512⟩ => ⟨h3264, h3274, h4512⟩

theorem CC96_equiv (G : Type*) [Magma G] : ConjunctionClass96 G <-> ConjunctionClass96_long G :=
Iff.intro (CC96_implies_long G) (CC96_implied_by_long G)

theorem CC97_implies_long (G : Type*) [Magma G] (h : ConjunctionClass97 G) : ConjunctionClass97_long G := by
  obtain ⟨eq3278, eq4512⟩ := h
  have eq1 := Equation3278_4512_implies_Equation1 G eq3278 eq4512
  have eq3253 := Equation3278_4512_implies_Equation3253 G eq3278 eq4512
  exact ⟨eq1, eq3253, eq3278, eq4512⟩

theorem CC97_implied_by_long (G : Type*) [Magma G] : ConjunctionClass97_long G -> ConjunctionClass97 G :=
fun ⟨_, _, h3278, h4512⟩ => ⟨h3278, h4512⟩

theorem CC97_equiv (G : Type*) [Magma G] : ConjunctionClass97 G <-> ConjunctionClass97_long G :=
Iff.intro (CC97_implies_long G) (CC97_implied_by_long G)

theorem CC98_implies_long (G : Type*) [Magma G] (h : ConjunctionClass98 G) : ConjunctionClass98_long G := by
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

theorem CC98_implied_by_long (G : Type*) [Magma G] : ConjunctionClass98_long G -> ConjunctionClass98 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, h3292, _, _, _, _, h4512⟩ => ⟨h3292, h4512⟩

theorem CC98_equiv (G : Type*) [Magma G] : ConjunctionClass98 G <-> ConjunctionClass98_long G :=
Iff.intro (CC98_implies_long G) (CC98_implied_by_long G)

theorem CC99_implies_long (G : Type*) [Magma G] (h : ConjunctionClass99 G) : ConjunctionClass99_long G := by
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

theorem CC99_implied_by_long (G : Type*) [Magma G] : ConjunctionClass99_long G -> ConjunctionClass99 G :=
fun ⟨_, _, _, _, _, _, _, _, h3264, _, _, h3292, _, _, _, _, h4512⟩ => ⟨h3264, h3292, h4512⟩

theorem CC99_equiv (G : Type*) [Magma G] : ConjunctionClass99 G <-> ConjunctionClass99_long G :=
Iff.intro (CC99_implies_long G) (CC99_implied_by_long G)

theorem CC100_implies_long (G : Type*) [Magma G] (h : ConjunctionClass100 G) : ConjunctionClass100_long G := by
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

theorem CC100_implied_by_long (G : Type*) [Magma G] : ConjunctionClass100_long G -> ConjunctionClass100 G :=
fun ⟨_, _, _, _, _, _, _, _, _, h3274, _, h3292, _, _, _, _, h4512⟩ => ⟨h3274, h3292, h4512⟩

theorem CC100_equiv (G : Type*) [Magma G] : ConjunctionClass100 G <-> ConjunctionClass100_long G :=
Iff.intro (CC100_implies_long G) (CC100_implied_by_long G)

theorem CC101_implies_long (G : Type*) [Magma G] (h : ConjunctionClass101 G) : ConjunctionClass101_long G := by
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

theorem CC101_implied_by_long (G : Type*) [Magma G] : ConjunctionClass101_long G -> ConjunctionClass101 G :=
fun ⟨_, _, _, _, _, _, _, _, h3264, _, h3274, _, h3292, _, _, _, _, h4512⟩ => ⟨h3264, h3274, h3292, h4512⟩

theorem CC101_equiv (G : Type*) [Magma G] : ConjunctionClass101 G <-> ConjunctionClass101_long G :=
Iff.intro (CC101_implies_long G) (CC101_implied_by_long G)

theorem CC102_implies_long (G : Type*) [Magma G] (h : ConjunctionClass102 G) : ConjunctionClass102_long G := by
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

theorem CC102_implied_by_long (G : Type*) [Magma G] : ConjunctionClass102_long G -> ConjunctionClass102 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3300, _, _, _, _, h4512⟩ => ⟨h3300, h4512⟩

theorem CC102_equiv (G : Type*) [Magma G] : ConjunctionClass102 G <-> ConjunctionClass102_long G :=
Iff.intro (CC102_implies_long G) (CC102_implied_by_long G)

theorem CC103_implies_long (G : Type*) [Magma G] (h : ConjunctionClass103 G) : ConjunctionClass103_long G := by
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

theorem CC103_implied_by_long (G : Type*) [Magma G] : ConjunctionClass103_long G -> ConjunctionClass103 G :=
fun ⟨_, _, h309, _, _, _, _, _, _, _, _, _, _, _, h3300, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h309, h3300, h4512⟩

theorem CC103_equiv (G : Type*) [Magma G] : ConjunctionClass103 G <-> ConjunctionClass103_long G :=
Iff.intro (CC103_implies_long G) (CC103_implied_by_long G)

theorem CC104_implies_long (G : Type*) [Magma G] (h : ConjunctionClass104 G) : ConjunctionClass104_long G := by
  obtain ⟨eq3306, eq4512⟩ := h
  have eq1 := Equation3306_4512_implies_Equation1 G eq3306 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact ⟨eq1, eq3253, eq3306, eq4512⟩

theorem CC104_implied_by_long (G : Type*) [Magma G] : ConjunctionClass104_long G -> ConjunctionClass104 G :=
fun ⟨_, _, h3306, h4512⟩ => ⟨h3306, h4512⟩

theorem CC104_equiv (G : Type*) [Magma G] : ConjunctionClass104 G <-> ConjunctionClass104_long G :=
Iff.intro (CC104_implies_long G) (CC104_implied_by_long G)

theorem CC105_implies_long (G : Type*) [Magma G] (h : ConjunctionClass105 G) : ConjunctionClass105_long G := by
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

theorem CC105_implied_by_long (G : Type*) [Magma G] : ConjunctionClass105_long G -> ConjunctionClass105 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, h3306, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h3306, h4512⟩

theorem CC105_equiv (G : Type*) [Magma G] : ConjunctionClass105 G <-> ConjunctionClass105_long G :=
Iff.intro (CC105_implies_long G) (CC105_implied_by_long G)

theorem CC106_implies_long (G : Type*) [Magma G] (h : ConjunctionClass106 G) : ConjunctionClass106_long G := by
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

theorem CC106_implied_by_long (G : Type*) [Magma G] : ConjunctionClass106_long G -> ConjunctionClass106 G :=
fun ⟨_, h43, _, h3306, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h3306, h4512⟩

theorem CC106_equiv (G : Type*) [Magma G] : ConjunctionClass106 G <-> ConjunctionClass106_long G :=
Iff.intro (CC106_implies_long G) (CC106_implied_by_long G)

theorem CC107_implies_long (G : Type*) [Magma G] (h : ConjunctionClass107 G) : ConjunctionClass107_long G := by
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

theorem CC107_implied_by_long (G : Type*) [Magma G] : ConjunctionClass107_long G -> ConjunctionClass107 G :=
fun ⟨_, _, h3256, _, _, h3306, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3256, h3306, h4512⟩

theorem CC107_equiv (G : Type*) [Magma G] : ConjunctionClass107 G <-> ConjunctionClass107_long G :=
Iff.intro (CC107_implies_long G) (CC107_implied_by_long G)

theorem CC108_implies_long (G : Type*) [Magma G] (h : ConjunctionClass108 G) : ConjunctionClass108_long G := by
  obtain ⟨eq3261, eq3306, eq4512⟩ := h
  have eq3334 := Equation3261_3306_4512_implies_Equation3334 G eq3261 eq3306 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq3319 := Equation3334_4512_implies_Equation3319 G eq3334 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3306, eq3319, eq3334, eq4512⟩

theorem CC108_implied_by_long (G : Type*) [Magma G] : ConjunctionClass108_long G -> ConjunctionClass108 G :=
fun ⟨_, _, h3261, h3306, _, _, h4512⟩ => ⟨h3261, h3306, h4512⟩

theorem CC108_equiv (G : Type*) [Magma G] : ConjunctionClass108 G <-> ConjunctionClass108_long G :=
Iff.intro (CC108_implies_long G) (CC108_implied_by_long G)

theorem CC109_implies_long (G : Type*) [Magma G] (h : ConjunctionClass109 G) : ConjunctionClass109_long G := by
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

theorem CC109_implied_by_long (G : Type*) [Magma G] : ConjunctionClass109_long G -> ConjunctionClass109 G :=
fun ⟨_, _, _, h3271, _, h3306, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h3271, h3306, h4512⟩

theorem CC109_equiv (G : Type*) [Magma G] : ConjunctionClass109 G <-> ConjunctionClass109_long G :=
Iff.intro (CC109_implies_long G) (CC109_implied_by_long G)

theorem CC110_implies_long (G : Type*) [Magma G] (h : ConjunctionClass110 G) : ConjunctionClass110_long G := by
  obtain ⟨eq3278, eq3306, eq4512⟩ := h
  have eq3414 := Equation3278_3306_4512_implies_Equation3414 G eq3278 eq3306 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3414_4512_implies_Equation3253 G eq3414 eq4512
  have eq3353 := Equation3414_4512_implies_Equation3353 G eq3414 eq4512
  exact ⟨eq1, eq3253, eq3278, eq3306, eq3353, eq3414, eq4512⟩

theorem CC110_implied_by_long (G : Type*) [Magma G] : ConjunctionClass110_long G -> ConjunctionClass110 G :=
fun ⟨_, _, h3278, h3306, _, _, h4512⟩ => ⟨h3278, h3306, h4512⟩

theorem CC110_equiv (G : Type*) [Magma G] : ConjunctionClass110 G <-> ConjunctionClass110_long G :=
Iff.intro (CC110_implies_long G) (CC110_implied_by_long G)

theorem CC111_implies_long (G : Type*) [Magma G] (h : ConjunctionClass111 G) : ConjunctionClass111_long G := by
  obtain ⟨eq3308, eq4512⟩ := h
  have eq1 := Equation3308_4512_implies_Equation1 G eq3308 eq4512
  have eq3253 := Equation3308_4512_implies_Equation3253 G eq3308 eq4512
  have eq3306 := Equation3308_4512_implies_Equation3306 G eq3308 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq3319 := Equation3308_4512_implies_Equation3319 G eq3308 eq4512
  have eq4283 := Equation3308_4512_implies_Equation4283 G eq3308 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4512⟩

theorem CC111_implied_by_long (G : Type*) [Magma G] : ConjunctionClass111_long G -> ConjunctionClass111 G :=
fun ⟨_, _, _, h3308, _, _, _, h4512⟩ => ⟨h3308, h4512⟩

theorem CC111_equiv (G : Type*) [Magma G] : ConjunctionClass111 G <-> ConjunctionClass111_long G :=
Iff.intro (CC111_implies_long G) (CC111_implied_by_long G)

theorem CC112_implies_long (G : Type*) [Magma G] (h : ConjunctionClass112 G) : ConjunctionClass112_long G := by
  obtain ⟨eq8, eq3308, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq4283 := Equation3308_4512_implies_Equation4283 G eq3308 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4512⟩

theorem CC112_implied_by_long (G : Type*) [Magma G] : ConjunctionClass112_long G -> ConjunctionClass112 G :=
fun ⟨_, h8, _, _, _, h3308, _, _, _, h4512⟩ => ⟨h8, h3308, h4512⟩

theorem CC112_equiv (G : Type*) [Magma G] : ConjunctionClass112 G <-> ConjunctionClass112_long G :=
Iff.intro (CC112_implies_long G) (CC112_implied_by_long G)

theorem CC113_implies_long (G : Type*) [Magma G] (h : ConjunctionClass113 G) : ConjunctionClass113_long G := by
  obtain ⟨eq3315, eq4512⟩ := h
  have eq1 := Equation3315_4512_implies_Equation1 G eq3315 eq4512
  have eq3253 := Equation3315_4512_implies_Equation3253 G eq3315 eq4512
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact ⟨eq1, eq3253, eq3315, eq3319, eq4512⟩

theorem CC113_implied_by_long (G : Type*) [Magma G] : ConjunctionClass113_long G -> ConjunctionClass113 G :=
fun ⟨_, _, h3315, _, h4512⟩ => ⟨h3315, h4512⟩

theorem CC113_equiv (G : Type*) [Magma G] : ConjunctionClass113 G <-> ConjunctionClass113_long G :=
Iff.intro (CC113_implies_long G) (CC113_implied_by_long G)

theorem CC114_implies_long (G : Type*) [Magma G] (h : ConjunctionClass114 G) : ConjunctionClass114_long G := by
  obtain ⟨eq8, eq3315, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3315, eq3319, eq4512⟩

theorem CC114_implied_by_long (G : Type*) [Magma G] : ConjunctionClass114_long G -> ConjunctionClass114 G :=
fun ⟨_, h8, _, _, _, h3315, _, h4512⟩ => ⟨h8, h3315, h4512⟩

theorem CC114_equiv (G : Type*) [Magma G] : ConjunctionClass114 G <-> ConjunctionClass114_long G :=
Iff.intro (CC114_implies_long G) (CC114_implied_by_long G)

theorem CC115_implies_long (G : Type*) [Magma G] (h : ConjunctionClass115 G) : ConjunctionClass115_long G := by
  obtain ⟨eq3256, eq3315, eq4512⟩ := h
  have eq3323 := Equation3256_3315_4512_implies_Equation3323 G eq3256 eq3315 eq4512
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3315, eq3319, eq3323, eq4512⟩

theorem CC115_implied_by_long (G : Type*) [Magma G] : ConjunctionClass115_long G -> ConjunctionClass115 G :=
fun ⟨_, _, h3256, h3315, _, _, h4512⟩ => ⟨h3256, h3315, h4512⟩

theorem CC115_equiv (G : Type*) [Magma G] : ConjunctionClass115 G <-> ConjunctionClass115_long G :=
Iff.intro (CC115_implies_long G) (CC115_implied_by_long G)

theorem CC116_implies_long (G : Type*) [Magma G] (h : ConjunctionClass116 G) : ConjunctionClass116_long G := by
  obtain ⟨eq3306, eq3315, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq3319 := Equation3315_4512_implies_Equation3319 G eq3315 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3315, eq3319, eq4512⟩

theorem CC116_implied_by_long (G : Type*) [Magma G] : ConjunctionClass116_long G -> ConjunctionClass116 G :=
fun ⟨_, _, h3306, h3315, _, h4512⟩ => ⟨h3306, h3315, h4512⟩

theorem CC116_equiv (G : Type*) [Magma G] : ConjunctionClass116 G <-> ConjunctionClass116_long G :=
Iff.intro (CC116_implies_long G) (CC116_implied_by_long G)

theorem CC117_implies_long (G : Type*) [Magma G] (h : ConjunctionClass117 G) : ConjunctionClass117_long G := by
  obtain ⟨eq3316, eq4512⟩ := h
  have eq1 := Equation3316_4512_implies_Equation1 G eq3316 eq4512
  have eq307 := Equation3316_4512_implies_Equation307 G eq3316 eq4512
  have eq3253 := Equation3316_4512_implies_Equation3253 G eq3316 eq4512
  exact ⟨eq1, eq307, eq3253, eq3316, eq4512⟩

theorem CC117_implied_by_long (G : Type*) [Magma G] : ConjunctionClass117_long G -> ConjunctionClass117 G :=
fun ⟨_, _, _, h3316, h4512⟩ => ⟨h3316, h4512⟩

theorem CC117_equiv (G : Type*) [Magma G] : ConjunctionClass117 G <-> ConjunctionClass117_long G :=
Iff.intro (CC117_implies_long G) (CC117_implied_by_long G)

theorem CC118_implies_long (G : Type*) [Magma G] (h : ConjunctionClass118 G) : ConjunctionClass118_long G := by
  obtain ⟨eq323, eq3316, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq3316, eq4512⟩

theorem CC118_implied_by_long (G : Type*) [Magma G] : ConjunctionClass118_long G -> ConjunctionClass118 G :=
fun ⟨_, _, h323, _, _, h3316, h4512⟩ => ⟨h323, h3316, h4512⟩

theorem CC118_equiv (G : Type*) [Magma G] : ConjunctionClass118 G <-> ConjunctionClass118_long G :=
Iff.intro (CC118_implies_long G) (CC118_implied_by_long G)

theorem CC119_implies_long (G : Type*) [Magma G] (h : ConjunctionClass119 G) : ConjunctionClass119_long G := by
  obtain ⟨eq326, eq3316, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation3316_4512_implies_Equation307 G eq3316 eq4512
  have eq3253 := Equation3316_4512_implies_Equation3253 G eq3316 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3316, eq3319, eq4512⟩

theorem CC119_implied_by_long (G : Type*) [Magma G] : ConjunctionClass119_long G -> ConjunctionClass119 G :=
fun ⟨_, _, h326, _, h3316, _, h4512⟩ => ⟨h326, h3316, h4512⟩

theorem CC119_equiv (G : Type*) [Magma G] : ConjunctionClass119 G <-> ConjunctionClass119_long G :=
Iff.intro (CC119_implies_long G) (CC119_implied_by_long G)

theorem CC120_implies_long (G : Type*) [Magma G] (h : ConjunctionClass120 G) : ConjunctionClass120_long G := by
  obtain ⟨eq3319, eq4512⟩ := h
  have eq1 := Equation3319_4512_implies_Equation1 G eq3319 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact ⟨eq1, eq3253, eq3319, eq4512⟩

theorem CC120_implied_by_long (G : Type*) [Magma G] : ConjunctionClass120_long G -> ConjunctionClass120 G :=
fun ⟨_, _, h3319, h4512⟩ => ⟨h3319, h4512⟩

theorem CC120_equiv (G : Type*) [Magma G] : ConjunctionClass120 G <-> ConjunctionClass120_long G :=
Iff.intro (CC120_implies_long G) (CC120_implied_by_long G)

theorem CC121_implies_long (G : Type*) [Magma G] (h : ConjunctionClass121 G) : ConjunctionClass121_long G := by
  obtain ⟨eq3306, eq3319, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq4512⟩

theorem CC121_implied_by_long (G : Type*) [Magma G] : ConjunctionClass121_long G -> ConjunctionClass121 G :=
fun ⟨_, _, h3306, h3319, h4512⟩ => ⟨h3306, h3319, h4512⟩

theorem CC121_equiv (G : Type*) [Magma G] : ConjunctionClass121 G <-> ConjunctionClass121_long G :=
Iff.intro (CC121_implies_long G) (CC121_implied_by_long G)

theorem CC122_implies_long (G : Type*) [Magma G] (h : ConjunctionClass122 G) : ConjunctionClass122_long G := by
  obtain ⟨eq3346, eq4512⟩ := h
  have eq1 := Equation3346_4512_implies_Equation1 G eq3346 eq4512
  have eq3253 := Equation3346_4512_implies_Equation3253 G eq3346 eq4512
  have eq3306 := Equation3346_4512_implies_Equation3306 G eq3346 eq4512
  have eq3319 := Equation3346_4512_implies_Equation3319 G eq3346 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  have eq4320 := Equation3346_4512_implies_Equation4320 G eq3346 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4512⟩

theorem CC122_implied_by_long (G : Type*) [Magma G] : ConjunctionClass122_long G -> ConjunctionClass122 G :=
fun ⟨_, _, _, _, h3346, _, _, h4512⟩ => ⟨h3346, h4512⟩

theorem CC122_equiv (G : Type*) [Magma G] : ConjunctionClass122 G <-> ConjunctionClass122_long G :=
Iff.intro (CC122_implies_long G) (CC122_implied_by_long G)

theorem CC123_implies_long (G : Type*) [Magma G] (h : ConjunctionClass123 G) : ConjunctionClass123_long G := by
  obtain ⟨eq8, eq3346, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  have eq4320 := Equation3346_4512_implies_Equation4320 G eq3346 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4512⟩

theorem CC123_implied_by_long (G : Type*) [Magma G] : ConjunctionClass123_long G -> ConjunctionClass123 G :=
fun ⟨_, h8, _, _, _, _, h3346, _, _, h4512⟩ => ⟨h8, h3346, h4512⟩

theorem CC123_equiv (G : Type*) [Magma G] : ConjunctionClass123 G <-> ConjunctionClass123_long G :=
Iff.intro (CC123_implies_long G) (CC123_implied_by_long G)

theorem CC124_implies_long (G : Type*) [Magma G] (h : ConjunctionClass124 G) : ConjunctionClass124_long G := by
  obtain ⟨eq3353, eq4512⟩ := h
  have eq1 := Equation3353_4512_implies_Equation1 G eq3353 eq4512
  have eq3253 := Equation3353_4512_implies_Equation3253 G eq3353 eq4512
  have eq3306 := Equation3353_4512_implies_Equation3306 G eq3353 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3353, eq4512⟩

theorem CC124_implied_by_long (G : Type*) [Magma G] : ConjunctionClass124_long G -> ConjunctionClass124 G :=
fun ⟨_, _, _, h3353, h4512⟩ => ⟨h3353, h4512⟩

theorem CC124_equiv (G : Type*) [Magma G] : ConjunctionClass124 G <-> ConjunctionClass124_long G :=
Iff.intro (CC124_implies_long G) (CC124_implied_by_long G)

theorem CC125_implies_long (G : Type*) [Magma G] (h : ConjunctionClass125 G) : ConjunctionClass125_long G := by
  obtain ⟨eq8, eq3353, eq4512⟩ := h
  have eq1 := Equation8_4512_implies_Equation1 G eq8 eq4512
  have eq411 := Equation8_4512_implies_Equation411 G eq8 eq4512
  have eq3253 := Equation8_4512_implies_Equation3253 G eq8 eq4512
  have eq3306 := Equation8_4512_implies_Equation3306 G eq8 eq4512
  have eq3319 := Equation8_4512_implies_Equation3319 G eq8 eq4512
  exact ⟨eq1, eq8, eq411, eq3253, eq3306, eq3319, eq3353, eq4512⟩

theorem CC125_implied_by_long (G : Type*) [Magma G] : ConjunctionClass125_long G -> ConjunctionClass125 G :=
fun ⟨_, h8, _, _, _, _, h3353, h4512⟩ => ⟨h8, h3353, h4512⟩

theorem CC125_equiv (G : Type*) [Magma G] : ConjunctionClass125 G <-> ConjunctionClass125_long G :=
Iff.intro (CC125_implies_long G) (CC125_implied_by_long G)

theorem CC126_implies_long (G : Type*) [Magma G] (h : ConjunctionClass126 G) : ConjunctionClass126_long G := by
  obtain ⟨eq3319, eq3353, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3353_4512_implies_Equation3253 G eq3353 eq4512
  have eq3306 := Equation3353_4512_implies_Equation3306 G eq3353 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq3353, eq4512⟩

theorem CC126_implied_by_long (G : Type*) [Magma G] : ConjunctionClass126_long G -> ConjunctionClass126 G :=
fun ⟨_, _, _, h3319, h3353, h4512⟩ => ⟨h3319, h3353, h4512⟩

theorem CC126_equiv (G : Type*) [Magma G] : ConjunctionClass126 G <-> ConjunctionClass126_long G :=
Iff.intro (CC126_implies_long G) (CC126_implied_by_long G)

theorem CC127_implies_long (G : Type*) [Magma G] (h : ConjunctionClass127 G) : ConjunctionClass127_long G := by
  obtain ⟨eq4268, eq4512⟩ := h
  have eq1 := Equation4268_4512_implies_Equation1 G eq4268 eq4512
  exact ⟨eq1, eq4268, eq4512⟩

theorem CC127_implied_by_long (G : Type*) [Magma G] : ConjunctionClass127_long G -> ConjunctionClass127 G :=
fun ⟨_, h4268, h4512⟩ => ⟨h4268, h4512⟩

theorem CC127_equiv (G : Type*) [Magma G] : ConjunctionClass127 G <-> ConjunctionClass127_long G :=
Iff.intro (CC127_implies_long G) (CC127_implied_by_long G)

theorem CC128_implies_long (G : Type*) [Magma G] (h : ConjunctionClass128 G) : ConjunctionClass128_long G := by
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

theorem CC128_implied_by_long (G : Type*) [Magma G] : ConjunctionClass128_long G -> ConjunctionClass128 G :=
fun ⟨_, h43, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4268, h4512⟩

theorem CC128_equiv (G : Type*) [Magma G] : ConjunctionClass128 G <-> ConjunctionClass128_long G :=
Iff.intro (CC128_implies_long G) (CC128_implied_by_long G)

theorem CC129_implies_long (G : Type*) [Magma G] (h : ConjunctionClass129 G) : ConjunctionClass129_long G := by
  obtain ⟨eq4269, eq4512⟩ := h
  have eq1 := Equation4269_4512_implies_Equation1 G eq4269 eq4512
  exact ⟨eq1, eq4269, eq4512⟩

theorem CC129_implied_by_long (G : Type*) [Magma G] : ConjunctionClass129_long G -> ConjunctionClass129 G :=
fun ⟨_, h4269, h4512⟩ => ⟨h4269, h4512⟩

theorem CC129_equiv (G : Type*) [Magma G] : ConjunctionClass129 G <-> ConjunctionClass129_long G :=
Iff.intro (CC129_implies_long G) (CC129_implied_by_long G)

theorem CC130_implies_long (G : Type*) [Magma G] (h : ConjunctionClass130 G) : ConjunctionClass130_long G := by
  obtain ⟨eq4268, eq4269, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4283, eq4286, eq4512⟩

theorem CC130_implied_by_long (G : Type*) [Magma G] : ConjunctionClass130_long G -> ConjunctionClass130 G :=
fun ⟨_, h4268, h4269, _, _, h4512⟩ => ⟨h4268, h4269, h4512⟩

theorem CC130_equiv (G : Type*) [Magma G] : ConjunctionClass130 G <-> ConjunctionClass130_long G :=
Iff.intro (CC130_implies_long G) (CC130_implied_by_long G)

theorem CC131_implies_long (G : Type*) [Magma G] (h : ConjunctionClass131 G) : ConjunctionClass131_long G := by
  obtain ⟨eq4270, eq4512⟩ := h
  have eq1 := Equation4270_4512_implies_Equation1 G eq4270 eq4512
  exact ⟨eq1, eq4270, eq4512⟩

theorem CC131_implied_by_long (G : Type*) [Magma G] : ConjunctionClass131_long G -> ConjunctionClass131 G :=
fun ⟨_, h4270, h4512⟩ => ⟨h4270, h4512⟩

theorem CC131_equiv (G : Type*) [Magma G] : ConjunctionClass131 G <-> ConjunctionClass131_long G :=
Iff.intro (CC131_implies_long G) (CC131_implied_by_long G)

theorem CC132_implies_long (G : Type*) [Magma G] (h : ConjunctionClass132 G) : ConjunctionClass132_long G := by
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

theorem CC132_implied_by_long (G : Type*) [Magma G] : ConjunctionClass132_long G -> ConjunctionClass132 G :=
fun ⟨_, h43, h4270, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4270, h4512⟩

theorem CC132_equiv (G : Type*) [Magma G] : ConjunctionClass132 G <-> ConjunctionClass132_long G :=
Iff.intro (CC132_implies_long G) (CC132_implied_by_long G)

theorem CC133_implies_long (G : Type*) [Magma G] (h : ConjunctionClass133 G) : ConjunctionClass133_long G := by
  obtain ⟨eq4268, eq4270, eq4512⟩ := h
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  exact ⟨eq1, eq4268, eq4270, eq4284, eq4288, eq4512⟩

theorem CC133_implied_by_long (G : Type*) [Magma G] : ConjunctionClass133_long G -> ConjunctionClass133 G :=
fun ⟨_, h4268, h4270, _, _, h4512⟩ => ⟨h4268, h4270, h4512⟩

theorem CC133_equiv (G : Type*) [Magma G] : ConjunctionClass133 G <-> ConjunctionClass133_long G :=
Iff.intro (CC133_implies_long G) (CC133_implied_by_long G)

theorem CC134_implies_long (G : Type*) [Magma G] (h : ConjunctionClass134 G) : ConjunctionClass134_long G := by
  obtain ⟨eq4269, eq4270, eq4512⟩ := h
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  exact ⟨eq1, eq4269, eq4270, eq4314, eq4318, eq4512⟩

theorem CC134_implied_by_long (G : Type*) [Magma G] : ConjunctionClass134_long G -> ConjunctionClass134 G :=
fun ⟨_, h4269, h4270, _, _, h4512⟩ => ⟨h4269, h4270, h4512⟩

theorem CC134_equiv (G : Type*) [Magma G] : ConjunctionClass134 G <-> ConjunctionClass134_long G :=
Iff.intro (CC134_implies_long G) (CC134_implied_by_long G)

theorem CC135_implies_long (G : Type*) [Magma G] (h : ConjunctionClass135 G) : ConjunctionClass135_long G := by
  obtain ⟨eq4268, eq4269, eq4270, eq4512⟩ := h
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  have eq4288 := Equation4268_4270_4512_implies_Equation4288 G eq4268 eq4270 eq4512
  have eq4318 := Equation4269_4270_4512_implies_Equation4318 G eq4269 eq4270 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4284 := Equation4288_4512_implies_Equation4284 G eq4288 eq4512
  have eq4314 := Equation4318_4512_implies_Equation4314 G eq4318 eq4512
  have eq4283 := Equation4286_4512_implies_Equation4283 G eq4286 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4270, eq4283, eq4284, eq4286, eq4288, eq4314, eq4318, eq4512⟩

theorem CC135_implied_by_long (G : Type*) [Magma G] : ConjunctionClass135_long G -> ConjunctionClass135 G :=
fun ⟨_, h4268, h4269, h4270, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4269, h4270, h4512⟩

theorem CC135_equiv (G : Type*) [Magma G] : ConjunctionClass135 G <-> ConjunctionClass135_long G :=
Iff.intro (CC135_implies_long G) (CC135_implied_by_long G)

theorem CC136_implies_long (G : Type*) [Magma G] (h : ConjunctionClass136 G) : ConjunctionClass136_long G := by
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

theorem CC136_implied_by_long (G : Type*) [Magma G] : ConjunctionClass136_long G -> ConjunctionClass136 G :=
fun ⟨_, _, _, _, h4271, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4271, h4512⟩

theorem CC136_equiv (G : Type*) [Magma G] : ConjunctionClass136 G <-> ConjunctionClass136_long G :=
Iff.intro (CC136_implies_long G) (CC136_implied_by_long G)

theorem CC137_implies_long (G : Type*) [Magma G] (h : ConjunctionClass137 G) : ConjunctionClass137_long G := by
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

theorem CC137_implied_by_long (G : Type*) [Magma G] : ConjunctionClass137_long G -> ConjunctionClass137 G :=
fun ⟨_, h43, _, _, _, h4271, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4271, h4512⟩

theorem CC137_equiv (G : Type*) [Magma G] : ConjunctionClass137 G <-> ConjunctionClass137_long G :=
Iff.intro (CC137_implies_long G) (CC137_implied_by_long G)

theorem CC138_implies_long (G : Type*) [Magma G] (h : ConjunctionClass138 G) : ConjunctionClass138_long G := by
  obtain ⟨eq4272, eq4512⟩ := h
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  exact ⟨eq1, eq4272, eq4512⟩

theorem CC138_implied_by_long (G : Type*) [Magma G] : ConjunctionClass138_long G -> ConjunctionClass138 G :=
fun ⟨_, h4272, h4512⟩ => ⟨h4272, h4512⟩

theorem CC138_equiv (G : Type*) [Magma G] : ConjunctionClass138 G <-> ConjunctionClass138_long G :=
Iff.intro (CC138_implies_long G) (CC138_implied_by_long G)

theorem CC139_implies_long (G : Type*) [Magma G] (h : ConjunctionClass139 G) : ConjunctionClass139_long G := by
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

theorem CC139_implied_by_long (G : Type*) [Magma G] : ConjunctionClass139_long G -> ConjunctionClass139 G :=
fun ⟨_, h4268, _, h4272, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4272, h4512⟩

theorem CC139_equiv (G : Type*) [Magma G] : ConjunctionClass139 G <-> ConjunctionClass139_long G :=
Iff.intro (CC139_implies_long G) (CC139_implied_by_long G)

theorem CC140_implies_long (G : Type*) [Magma G] (h : ConjunctionClass140 G) : ConjunctionClass140_long G := by
  obtain ⟨eq4269, eq4272, eq4512⟩ := h
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4320, eq4327, eq4512⟩

theorem CC140_implied_by_long (G : Type*) [Magma G] : ConjunctionClass140_long G -> ConjunctionClass140 G :=
fun ⟨_, h4269, h4272, _, _, h4512⟩ => ⟨h4269, h4272, h4512⟩

theorem CC140_equiv (G : Type*) [Magma G] : ConjunctionClass140 G <-> ConjunctionClass140_long G :=
Iff.intro (CC140_implies_long G) (CC140_implied_by_long G)

theorem CC141_implies_long (G : Type*) [Magma G] (h : ConjunctionClass141 G) : ConjunctionClass141_long G := by
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

theorem CC141_implied_by_long (G : Type*) [Magma G] : ConjunctionClass141_long G -> ConjunctionClass141 G :=
fun ⟨_, h4268, h4269, _, h4272, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4269, h4272, h4512⟩

theorem CC141_equiv (G : Type*) [Magma G] : ConjunctionClass141 G <-> ConjunctionClass141_long G :=
Iff.intro (CC141_implies_long G) (CC141_implied_by_long G)

theorem CC142_implies_long (G : Type*) [Magma G] (h : ConjunctionClass142 G) : ConjunctionClass142_long G := by
  obtain ⟨eq4270, eq4272, eq4512⟩ := h
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4343, eq4512⟩

theorem CC142_implied_by_long (G : Type*) [Magma G] : ConjunctionClass142_long G -> ConjunctionClass142 G :=
fun ⟨_, h4270, h4272, _, _, _, h4512⟩ => ⟨h4270, h4272, h4512⟩

theorem CC142_equiv (G : Type*) [Magma G] : ConjunctionClass142 G <-> ConjunctionClass142_long G :=
Iff.intro (CC142_implies_long G) (CC142_implied_by_long G)

theorem CC143_implies_long (G : Type*) [Magma G] (h : ConjunctionClass143 G) : ConjunctionClass143_long G := by
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

theorem CC143_implied_by_long (G : Type*) [Magma G] : ConjunctionClass143_long G -> ConjunctionClass143 G :=
fun ⟨_, h4269, h4270, h4272, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4269, h4270, h4272, h4512⟩

theorem CC143_equiv (G : Type*) [Magma G] : ConjunctionClass143 G <-> ConjunctionClass143_long G :=
Iff.intro (CC143_implies_long G) (CC143_implied_by_long G)

theorem CC144_implies_long (G : Type*) [Magma G] (h : ConjunctionClass144 G) : ConjunctionClass144_long G := by
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

theorem CC144_implied_by_long (G : Type*) [Magma G] : ConjunctionClass144_long G -> ConjunctionClass144 G :=
fun ⟨_, _, _, _, h4271, h4272, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4271, h4272, h4512⟩

theorem CC144_equiv (G : Type*) [Magma G] : ConjunctionClass144 G <-> ConjunctionClass144_long G :=
Iff.intro (CC144_implies_long G) (CC144_implied_by_long G)

theorem CC145_implies_long (G : Type*) [Magma G] (h : ConjunctionClass145 G) : ConjunctionClass145_long G := by
  obtain ⟨eq4273, eq4512⟩ := h
  have eq1 := Equation4273_4512_implies_Equation1 G eq4273 eq4512
  exact ⟨eq1, eq4273, eq4512⟩

theorem CC145_implied_by_long (G : Type*) [Magma G] : ConjunctionClass145_long G -> ConjunctionClass145 G :=
fun ⟨_, h4273, h4512⟩ => ⟨h4273, h4512⟩

theorem CC145_equiv (G : Type*) [Magma G] : ConjunctionClass145 G <-> ConjunctionClass145_long G :=
Iff.intro (CC145_implies_long G) (CC145_implied_by_long G)

theorem CC146_implies_long (G : Type*) [Magma G] (h : ConjunctionClass146 G) : ConjunctionClass146_long G := by
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

theorem CC146_implied_by_long (G : Type*) [Magma G] : ConjunctionClass146_long G -> ConjunctionClass146 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, h4273, _, _, _, _, _, _, _, h4512⟩ => ⟨h40, h4273, h4512⟩

theorem CC146_equiv (G : Type*) [Magma G] : ConjunctionClass146 G <-> ConjunctionClass146_long G :=
Iff.intro (CC146_implies_long G) (CC146_implied_by_long G)

theorem CC147_implies_long (G : Type*) [Magma G] (h : ConjunctionClass147 G) : ConjunctionClass147_long G := by
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

theorem CC147_implied_by_long (G : Type*) [Magma G] : ConjunctionClass147_long G -> ConjunctionClass147 G :=
fun ⟨_, h4268, _, h4273, _, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4268, h4273, h4512⟩

theorem CC147_equiv (G : Type*) [Magma G] : ConjunctionClass147 G <-> ConjunctionClass147_long G :=
Iff.intro (CC147_implies_long G) (CC147_implied_by_long G)

theorem CC148_implies_long (G : Type*) [Magma G] (h : ConjunctionClass148 G) : ConjunctionClass148_long G := by
  obtain ⟨eq4269, eq4273, eq4512⟩ := h
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4321, eq4512⟩

theorem CC148_implied_by_long (G : Type*) [Magma G] : ConjunctionClass148_long G -> ConjunctionClass148 G :=
fun ⟨_, h4269, h4273, _, _, _, h4512⟩ => ⟨h4269, h4273, h4512⟩

theorem CC148_equiv (G : Type*) [Magma G] : ConjunctionClass148 G <-> ConjunctionClass148_long G :=
Iff.intro (CC148_implies_long G) (CC148_implied_by_long G)

theorem CC149_implies_long (G : Type*) [Magma G] (h : ConjunctionClass149 G) : ConjunctionClass149_long G := by
  obtain ⟨eq4270, eq4273, eq4512⟩ := h
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4320, eq4325, eq4512⟩

theorem CC149_implied_by_long (G : Type*) [Magma G] : ConjunctionClass149_long G -> ConjunctionClass149 G :=
fun ⟨_, h4270, h4273, _, _, h4512⟩ => ⟨h4270, h4273, h4512⟩

theorem CC149_equiv (G : Type*) [Magma G] : ConjunctionClass149 G <-> ConjunctionClass149_long G :=
Iff.intro (CC149_implies_long G) (CC149_implied_by_long G)

theorem CC150_implies_long (G : Type*) [Magma G] (h : ConjunctionClass150 G) : ConjunctionClass150_long G := by
  obtain ⟨eq4275, eq4512⟩ := h
  have eq1 := Equation4275_4512_implies_Equation1 G eq4275 eq4512
  exact ⟨eq1, eq4275, eq4512⟩

theorem CC150_implied_by_long (G : Type*) [Magma G] : ConjunctionClass150_long G -> ConjunctionClass150 G :=
fun ⟨_, h4275, h4512⟩ => ⟨h4275, h4512⟩

theorem CC150_equiv (G : Type*) [Magma G] : ConjunctionClass150 G <-> ConjunctionClass150_long G :=
Iff.intro (CC150_implies_long G) (CC150_implied_by_long G)

theorem CC151_implies_long (G : Type*) [Magma G] (h : ConjunctionClass151 G) : ConjunctionClass151_long G := by
  obtain ⟨eq4268, eq4275, eq4512⟩ := h
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4512⟩

theorem CC151_implied_by_long (G : Type*) [Magma G] : ConjunctionClass151_long G -> ConjunctionClass151 G :=
fun ⟨_, h4268, h4275, _, _, _, h4512⟩ => ⟨h4268, h4275, h4512⟩

theorem CC151_equiv (G : Type*) [Magma G] : ConjunctionClass151 G <-> ConjunctionClass151_long G :=
Iff.intro (CC151_implies_long G) (CC151_implied_by_long G)

theorem CC152_implies_long (G : Type*) [Magma G] (h : ConjunctionClass152 G) : ConjunctionClass152_long G := by
  obtain ⟨eq4269, eq4275, eq4512⟩ := h
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  exact ⟨eq1, eq4269, eq4275, eq4291, eq4296, eq4512⟩

theorem CC152_implied_by_long (G : Type*) [Magma G] : ConjunctionClass152_long G -> ConjunctionClass152 G :=
fun ⟨_, h4269, h4275, _, _, h4512⟩ => ⟨h4269, h4275, h4512⟩

theorem CC152_equiv (G : Type*) [Magma G] : ConjunctionClass152 G <-> ConjunctionClass152_long G :=
Iff.intro (CC152_implies_long G) (CC152_implied_by_long G)

theorem CC153_implies_long (G : Type*) [Magma G] (h : ConjunctionClass153 G) : ConjunctionClass153_long G := by
  obtain ⟨eq4270, eq4275, eq4512⟩ := h
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4297_4512_implies_Equation4290 G eq4297 eq4512
  exact ⟨eq1, eq4270, eq4275, eq4290, eq4297, eq4512⟩

theorem CC153_implied_by_long (G : Type*) [Magma G] : ConjunctionClass153_long G -> ConjunctionClass153 G :=
fun ⟨_, h4270, h4275, _, _, h4512⟩ => ⟨h4270, h4275, h4512⟩

theorem CC153_equiv (G : Type*) [Magma G] : ConjunctionClass153 G <-> ConjunctionClass153_long G :=
Iff.intro (CC153_implies_long G) (CC153_implied_by_long G)

theorem CC154_implies_long (G : Type*) [Magma G] (h : ConjunctionClass154 G) : ConjunctionClass154_long G := by
  obtain ⟨eq4272, eq4275, eq4512⟩ := h
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4284 := Equation4304_4512_implies_Equation4284 G eq4304 eq4512
  exact ⟨eq1, eq4272, eq4275, eq4284, eq4304, eq4512⟩

theorem CC154_implied_by_long (G : Type*) [Magma G] : ConjunctionClass154_long G -> ConjunctionClass154 G :=
fun ⟨_, h4272, h4275, _, _, h4512⟩ => ⟨h4272, h4275, h4512⟩

theorem CC154_equiv (G : Type*) [Magma G] : ConjunctionClass154 G <-> ConjunctionClass154_long G :=
Iff.intro (CC154_implies_long G) (CC154_implied_by_long G)

theorem CC155_implies_long (G : Type*) [Magma G] (h : ConjunctionClass155 G) : ConjunctionClass155_long G := by
  obtain ⟨eq4269, eq4272, eq4275, eq4512⟩ := h
  have eq4304 := Equation4272_4275_4512_implies_Equation4304 G eq4272 eq4275 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  have eq4296 := Equation4269_4275_4512_implies_Equation4296 G eq4269 eq4275 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4320 := Equation4327_4512_implies_Equation4320 G eq4327 eq4512
  have eq4291 := Equation4296_4512_implies_Equation4291 G eq4296 eq4512
  have eq4284 := Equation4304_4512_implies_Equation4284 G eq4304 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4275, eq4284, eq4291, eq4296, eq4304, eq4320, eq4327, eq4512⟩

theorem CC155_implied_by_long (G : Type*) [Magma G] : ConjunctionClass155_long G -> ConjunctionClass155 G :=
fun ⟨_, h4269, h4272, h4275, _, _, _, _, _, _, h4512⟩ => ⟨h4269, h4272, h4275, h4512⟩

theorem CC155_equiv (G : Type*) [Magma G] : ConjunctionClass155 G <-> ConjunctionClass155_long G :=
Iff.intro (CC155_implies_long G) (CC155_implied_by_long G)

theorem CC156_implies_long (G : Type*) [Magma G] (h : ConjunctionClass156 G) : ConjunctionClass156_long G := by
  obtain ⟨eq4273, eq4275, eq4512⟩ := h
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  exact ⟨eq1, eq4273, eq4275, eq4283, eq4305, eq4512⟩

theorem CC156_implied_by_long (G : Type*) [Magma G] : ConjunctionClass156_long G -> ConjunctionClass156 G :=
fun ⟨_, h4273, h4275, _, _, h4512⟩ => ⟨h4273, h4275, h4512⟩

theorem CC156_equiv (G : Type*) [Magma G] : ConjunctionClass156 G <-> ConjunctionClass156_long G :=
Iff.intro (CC156_implies_long G) (CC156_implied_by_long G)

theorem CC157_implies_long (G : Type*) [Magma G] (h : ConjunctionClass157 G) : ConjunctionClass157_long G := by
  obtain ⟨eq4270, eq4273, eq4275, eq4512⟩ := h
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4325_4512_implies_Equation4320 G eq4325 eq4512
  have eq4290 := Equation4297_4512_implies_Equation4290 G eq4297 eq4512
  have eq4283 := Equation4305_4512_implies_Equation4283 G eq4305 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4275, eq4283, eq4290, eq4297, eq4305, eq4320, eq4325, eq4512⟩

theorem CC157_implied_by_long (G : Type*) [Magma G] : ConjunctionClass157_long G -> ConjunctionClass157 G :=
fun ⟨_, h4270, h4273, h4275, _, _, _, _, _, _, h4512⟩ => ⟨h4270, h4273, h4275, h4512⟩

theorem CC157_equiv (G : Type*) [Magma G] : ConjunctionClass157 G <-> ConjunctionClass157_long G :=
Iff.intro (CC157_implies_long G) (CC157_implied_by_long G)

theorem CC158_implies_long (G : Type*) [Magma G] (h : ConjunctionClass158 G) : ConjunctionClass158_long G := by
  obtain ⟨eq4276, eq4512⟩ := h
  have eq1 := Equation4276_4512_implies_Equation1 G eq4276 eq4512
  exact ⟨eq1, eq4276, eq4512⟩

theorem CC158_implied_by_long (G : Type*) [Magma G] : ConjunctionClass158_long G -> ConjunctionClass158 G :=
fun ⟨_, h4276, h4512⟩ => ⟨h4276, h4512⟩

theorem CC158_equiv (G : Type*) [Magma G] : ConjunctionClass158 G <-> ConjunctionClass158_long G :=
Iff.intro (CC158_implies_long G) (CC158_implied_by_long G)

theorem CC159_implies_long (G : Type*) [Magma G] (h : ConjunctionClass159 G) : ConjunctionClass159_long G := by
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

theorem CC159_implied_by_long (G : Type*) [Magma G] : ConjunctionClass159_long G -> ConjunctionClass159 G :=
fun ⟨_, h43, h4276, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4276, h4512⟩

theorem CC159_equiv (G : Type*) [Magma G] : ConjunctionClass159 G <-> ConjunctionClass159_long G :=
Iff.intro (CC159_implies_long G) (CC159_implied_by_long G)

theorem CC160_implies_long (G : Type*) [Magma G] (h : ConjunctionClass160 G) : ConjunctionClass160_long G := by
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

theorem CC160_implied_by_long (G : Type*) [Magma G] : ConjunctionClass160_long G -> ConjunctionClass160 G :=
fun ⟨_, _, _, _, h4278, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4278, h4512⟩

theorem CC160_equiv (G : Type*) [Magma G] : ConjunctionClass160 G <-> ConjunctionClass160_long G :=
Iff.intro (CC160_implies_long G) (CC160_implied_by_long G)

theorem CC161_implies_long (G : Type*) [Magma G] (h : ConjunctionClass161 G) : ConjunctionClass161_long G := by
  obtain ⟨eq4283, eq4512⟩ := h
  have eq1 := Equation4283_4512_implies_Equation1 G eq4283 eq4512
  exact ⟨eq1, eq4283, eq4512⟩

theorem CC161_implied_by_long (G : Type*) [Magma G] : ConjunctionClass161_long G -> ConjunctionClass161 G :=
fun ⟨_, h4283, h4512⟩ => ⟨h4283, h4512⟩

theorem CC161_equiv (G : Type*) [Magma G] : ConjunctionClass161 G <-> ConjunctionClass161_long G :=
Iff.intro (CC161_implies_long G) (CC161_implied_by_long G)

theorem CC162_implies_long (G : Type*) [Magma G] (h : ConjunctionClass162 G) : ConjunctionClass162_long G := by
  obtain ⟨eq47, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq47, eq4283, eq4512⟩

theorem CC162_implied_by_long (G : Type*) [Magma G] : ConjunctionClass162_long G -> ConjunctionClass162 G :=
fun ⟨_, h47, h4283, h4512⟩ => ⟨h47, h4283, h4512⟩

theorem CC162_equiv (G : Type*) [Magma G] : ConjunctionClass162 G <-> ConjunctionClass162_long G :=
Iff.intro (CC162_implies_long G) (CC162_implied_by_long G)

theorem CC163_implies_long (G : Type*) [Magma G] (h : ConjunctionClass163 G) : ConjunctionClass163_long G := by
  obtain ⟨eq56, eq4283, eq4512⟩ := h
  have eq4358 := Equation56_4283_4512_implies_Equation4358 G eq56 eq4283 eq4512
  have eq1 := Equation56_4512_implies_Equation1 G eq56 eq4512
  have eq47 := Equation56_4512_implies_Equation47 G eq56 eq4512
  exact ⟨eq1, eq47, eq56, eq4283, eq4358, eq4512⟩

theorem CC163_implied_by_long (G : Type*) [Magma G] : ConjunctionClass163_long G -> ConjunctionClass163 G :=
fun ⟨_, _, h56, h4283, _, h4512⟩ => ⟨h56, h4283, h4512⟩

theorem CC163_equiv (G : Type*) [Magma G] : ConjunctionClass163 G <-> ConjunctionClass163_long G :=
Iff.intro (CC163_implies_long G) (CC163_implied_by_long G)

theorem CC164_implies_long (G : Type*) [Magma G] (h : ConjunctionClass164 G) : ConjunctionClass164_long G := by
  obtain ⟨eq307, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4512⟩

theorem CC164_implied_by_long (G : Type*) [Magma G] : ConjunctionClass164_long G -> ConjunctionClass164 G :=
fun ⟨_, h307, _, h4283, h4512⟩ => ⟨h307, h4283, h4512⟩

theorem CC164_equiv (G : Type*) [Magma G] : ConjunctionClass164 G <-> ConjunctionClass164_long G :=
Iff.intro (CC164_implies_long G) (CC164_implied_by_long G)

theorem CC165_implies_long (G : Type*) [Magma G] (h : ConjunctionClass165 G) : ConjunctionClass165_long G := by
  obtain ⟨eq326, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4283, eq4512⟩

theorem CC165_implied_by_long (G : Type*) [Magma G] : ConjunctionClass165_long G -> ConjunctionClass165 G :=
fun ⟨_, _, h326, _, _, h4283, h4512⟩ => ⟨h326, h4283, h4512⟩

theorem CC165_equiv (G : Type*) [Magma G] : ConjunctionClass165 G <-> ConjunctionClass165_long G :=
Iff.intro (CC165_implies_long G) (CC165_implied_by_long G)

theorem CC166_implies_long (G : Type*) [Magma G] (h : ConjunctionClass166 G) : ConjunctionClass166_long G := by
  obtain ⟨eq411, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq411, eq4283, eq4512⟩

theorem CC166_implied_by_long (G : Type*) [Magma G] : ConjunctionClass166_long G -> ConjunctionClass166 G :=
fun ⟨_, h411, h4283, h4512⟩ => ⟨h411, h4283, h4512⟩

theorem CC166_equiv (G : Type*) [Magma G] : ConjunctionClass166 G <-> ConjunctionClass166_long G :=
Iff.intro (CC166_implies_long G) (CC166_implied_by_long G)

theorem CC167_implies_long (G : Type*) [Magma G] (h : ConjunctionClass167 G) : ConjunctionClass167_long G := by
  obtain ⟨eq440, eq4283, eq4512⟩ := h
  have eq4358 := Equation440_4283_4512_implies_Equation4358 G eq440 eq4283 eq4512
  have eq1 := Equation440_4512_implies_Equation1 G eq440 eq4512
  have eq411 := Equation440_4512_implies_Equation411 G eq440 eq4512
  exact ⟨eq1, eq411, eq440, eq4283, eq4358, eq4512⟩

theorem CC167_implied_by_long (G : Type*) [Magma G] : ConjunctionClass167_long G -> ConjunctionClass167 G :=
fun ⟨_, _, h440, h4283, _, h4512⟩ => ⟨h440, h4283, h4512⟩

theorem CC167_equiv (G : Type*) [Magma G] : ConjunctionClass167 G <-> ConjunctionClass167_long G :=
Iff.intro (CC167_implies_long G) (CC167_implied_by_long G)

theorem CC168_implies_long (G : Type*) [Magma G] (h : ConjunctionClass168 G) : ConjunctionClass168_long G := by
  obtain ⟨eq3253, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq3253, eq4283, eq4512⟩

theorem CC168_implied_by_long (G : Type*) [Magma G] : ConjunctionClass168_long G -> ConjunctionClass168 G :=
fun ⟨_, h3253, h4283, h4512⟩ => ⟨h3253, h4283, h4512⟩

theorem CC168_equiv (G : Type*) [Magma G] : ConjunctionClass168 G <-> ConjunctionClass168_long G :=
Iff.intro (CC168_implies_long G) (CC168_implied_by_long G)

theorem CC169_implies_long (G : Type*) [Magma G] (h : ConjunctionClass169 G) : ConjunctionClass169_long G := by
  obtain ⟨eq3256, eq4283, eq4512⟩ := h
  have eq3259 := Equation3256_4283_4512_implies_Equation3259 G eq3256 eq4283 eq4512
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq4270, eq4283, eq4512⟩

theorem CC169_implied_by_long (G : Type*) [Magma G] : ConjunctionClass169_long G -> ConjunctionClass169 G :=
fun ⟨_, _, h3256, _, _, _, h4283, h4512⟩ => ⟨h3256, h4283, h4512⟩

theorem CC169_equiv (G : Type*) [Magma G] : ConjunctionClass169 G <-> ConjunctionClass169_long G :=
Iff.intro (CC169_implies_long G) (CC169_implied_by_long G)

theorem CC170_implies_long (G : Type*) [Magma G] (h : ConjunctionClass170 G) : ConjunctionClass170_long G := by
  obtain ⟨eq3319, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact ⟨eq1, eq3253, eq3319, eq4283, eq4512⟩

theorem CC170_implied_by_long (G : Type*) [Magma G] : ConjunctionClass170_long G -> ConjunctionClass170 G :=
fun ⟨_, _, h3319, h4283, h4512⟩ => ⟨h3319, h4283, h4512⟩

theorem CC170_equiv (G : Type*) [Magma G] : ConjunctionClass170 G <-> ConjunctionClass170_long G :=
Iff.intro (CC170_implies_long G) (CC170_implied_by_long G)

theorem CC171_implies_long (G : Type*) [Magma G] (h : ConjunctionClass171 G) : ConjunctionClass171_long G := by
  obtain ⟨eq4270, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4270, eq4283, eq4512⟩

theorem CC171_implied_by_long (G : Type*) [Magma G] : ConjunctionClass171_long G -> ConjunctionClass171 G :=
fun ⟨_, h4270, h4283, h4512⟩ => ⟨h4270, h4283, h4512⟩

theorem CC171_equiv (G : Type*) [Magma G] : ConjunctionClass171 G <-> ConjunctionClass171_long G :=
Iff.intro (CC171_implies_long G) (CC171_implied_by_long G)

theorem CC172_implies_long (G : Type*) [Magma G] (h : ConjunctionClass172 G) : ConjunctionClass172_long G := by
  obtain ⟨eq4272, eq4283, eq4512⟩ := h
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4343, eq4512⟩

theorem CC172_implied_by_long (G : Type*) [Magma G] : ConjunctionClass172_long G -> ConjunctionClass172 G :=
fun ⟨_, _, h4272, _, _, h4283, _, h4512⟩ => ⟨h4272, h4283, h4512⟩

theorem CC172_equiv (G : Type*) [Magma G] : ConjunctionClass172 G <-> ConjunctionClass172_long G :=
Iff.intro (CC172_implies_long G) (CC172_implied_by_long G)

theorem CC173_implies_long (G : Type*) [Magma G] (h : ConjunctionClass173 G) : ConjunctionClass173_long G := by
  obtain ⟨eq4276, eq4283, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4512⟩

theorem CC173_implied_by_long (G : Type*) [Magma G] : ConjunctionClass173_long G -> ConjunctionClass173 G :=
fun ⟨_, h4276, h4283, h4512⟩ => ⟨h4276, h4283, h4512⟩

theorem CC173_equiv (G : Type*) [Magma G] : ConjunctionClass173 G <-> ConjunctionClass173_long G :=
Iff.intro (CC173_implies_long G) (CC173_implied_by_long G)

theorem CC174_implies_long (G : Type*) [Magma G] (h : ConjunctionClass174 G) : ConjunctionClass174_long G := by
  obtain ⟨eq4284, eq4512⟩ := h
  have eq1 := Equation4284_4512_implies_Equation1 G eq4284 eq4512
  exact ⟨eq1, eq4284, eq4512⟩

theorem CC174_implied_by_long (G : Type*) [Magma G] : ConjunctionClass174_long G -> ConjunctionClass174 G :=
fun ⟨_, h4284, h4512⟩ => ⟨h4284, h4512⟩

theorem CC174_equiv (G : Type*) [Magma G] : ConjunctionClass174 G <-> ConjunctionClass174_long G :=
Iff.intro (CC174_implies_long G) (CC174_implied_by_long G)

theorem CC175_implies_long (G : Type*) [Magma G] (h : ConjunctionClass175 G) : ConjunctionClass175_long G := by
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

theorem CC175_implied_by_long (G : Type*) [Magma G] : ConjunctionClass175_long G -> ConjunctionClass175 G :=
fun ⟨_, h43, _, h4284, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4284, h4512⟩

theorem CC175_equiv (G : Type*) [Magma G] : ConjunctionClass175 G <-> ConjunctionClass175_long G :=
Iff.intro (CC175_implies_long G) (CC175_implied_by_long G)

theorem CC176_implies_long (G : Type*) [Magma G] (h : ConjunctionClass176 G) : ConjunctionClass176_long G := by
  obtain ⟨eq307, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4512⟩

theorem CC176_implied_by_long (G : Type*) [Magma G] : ConjunctionClass176_long G -> ConjunctionClass176 G :=
fun ⟨_, h307, _, h4284, h4512⟩ => ⟨h307, h4284, h4512⟩

theorem CC176_equiv (G : Type*) [Magma G] : ConjunctionClass176 G <-> ConjunctionClass176_long G :=
Iff.intro (CC176_implies_long G) (CC176_implied_by_long G)

theorem CC177_implies_long (G : Type*) [Magma G] (h : ConjunctionClass177 G) : ConjunctionClass177_long G := by
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

theorem CC177_implied_by_long (G : Type*) [Magma G] : ConjunctionClass177_long G -> ConjunctionClass177 G :=
fun ⟨_, h43, h307, _, _, h4284, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h307, h4284, h4512⟩

theorem CC177_equiv (G : Type*) [Magma G] : ConjunctionClass177 G <-> ConjunctionClass177_long G :=
Iff.intro (CC177_implies_long G) (CC177_implied_by_long G)

theorem CC178_implies_long (G : Type*) [Magma G] (h : ConjunctionClass178 G) : ConjunctionClass178_long G := by
  obtain ⟨eq4269, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4269, eq4284, eq4512⟩

theorem CC178_implied_by_long (G : Type*) [Magma G] : ConjunctionClass178_long G -> ConjunctionClass178 G :=
fun ⟨_, h4269, h4284, h4512⟩ => ⟨h4269, h4284, h4512⟩

theorem CC178_equiv (G : Type*) [Magma G] : ConjunctionClass178 G <-> ConjunctionClass178_long G :=
Iff.intro (CC178_implies_long G) (CC178_implied_by_long G)

theorem CC179_implies_long (G : Type*) [Magma G] (h : ConjunctionClass179 G) : ConjunctionClass179_long G := by
  obtain ⟨eq4273, eq4284, eq4512⟩ := h
  have eq4269 := Equation4273_4284_4512_implies_Equation4269 G eq4273 eq4284 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4284, eq4321, eq4512⟩

theorem CC179_implied_by_long (G : Type*) [Magma G] : ConjunctionClass179_long G -> ConjunctionClass179 G :=
fun ⟨_, _, h4273, _, _, h4284, _, h4512⟩ => ⟨h4273, h4284, h4512⟩

theorem CC179_equiv (G : Type*) [Magma G] : ConjunctionClass179 G <-> ConjunctionClass179_long G :=
Iff.intro (CC179_implies_long G) (CC179_implied_by_long G)

theorem CC180_implies_long (G : Type*) [Magma G] (h : ConjunctionClass180 G) : ConjunctionClass180_long G := by
  obtain ⟨eq4276, eq4284, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4512⟩

theorem CC180_implied_by_long (G : Type*) [Magma G] : ConjunctionClass180_long G -> ConjunctionClass180 G :=
fun ⟨_, h4276, h4284, h4512⟩ => ⟨h4276, h4284, h4512⟩

theorem CC180_equiv (G : Type*) [Magma G] : ConjunctionClass180 G <-> ConjunctionClass180_long G :=
Iff.intro (CC180_implies_long G) (CC180_implied_by_long G)

theorem CC181_implies_long (G : Type*) [Magma G] (h : ConjunctionClass181 G) : ConjunctionClass181_long G := by
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

theorem CC181_implied_by_long (G : Type*) [Magma G] : ConjunctionClass181_long G -> ConjunctionClass181 G :=
fun ⟨_, h43, h4276, _, h4284, _, _, _, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h43, h4276, h4284, h4512⟩

theorem CC181_equiv (G : Type*) [Magma G] : ConjunctionClass181 G <-> ConjunctionClass181_long G :=
Iff.intro (CC181_implies_long G) (CC181_implied_by_long G)

theorem CC182_implies_long (G : Type*) [Magma G] (h : ConjunctionClass182 G) : ConjunctionClass182_long G := by
  obtain ⟨eq4283, eq4284, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4284, eq4314, eq4512⟩

theorem CC182_implied_by_long (G : Type*) [Magma G] : ConjunctionClass182_long G -> ConjunctionClass182 G :=
fun ⟨_, h4283, h4284, _, h4512⟩ => ⟨h4283, h4284, h4512⟩

theorem CC182_equiv (G : Type*) [Magma G] : ConjunctionClass182 G <-> ConjunctionClass182_long G :=
Iff.intro (CC182_implies_long G) (CC182_implied_by_long G)

theorem CC183_implies_long (G : Type*) [Magma G] (h : ConjunctionClass183 G) : ConjunctionClass183_long G := by
  obtain ⟨eq307, eq4283, eq4284, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4314, eq4512⟩

theorem CC183_implied_by_long (G : Type*) [Magma G] : ConjunctionClass183_long G -> ConjunctionClass183 G :=
fun ⟨_, h307, _, h4283, h4284, _, h4512⟩ => ⟨h307, h4283, h4284, h4512⟩

theorem CC183_equiv (G : Type*) [Magma G] : ConjunctionClass183 G <-> ConjunctionClass183_long G :=
Iff.intro (CC183_implies_long G) (CC183_implied_by_long G)

theorem CC184_implies_long (G : Type*) [Magma G] (h : ConjunctionClass184 G) : ConjunctionClass184_long G := by
  obtain ⟨eq4276, eq4283, eq4284, eq4512⟩ := h
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4314, eq4512⟩

theorem CC184_implied_by_long (G : Type*) [Magma G] : ConjunctionClass184_long G -> ConjunctionClass184 G :=
fun ⟨_, h4276, h4283, h4284, _, h4512⟩ => ⟨h4276, h4283, h4284, h4512⟩

theorem CC184_equiv (G : Type*) [Magma G] : ConjunctionClass184 G <-> ConjunctionClass184_long G :=
Iff.intro (CC184_implies_long G) (CC184_implied_by_long G)

theorem CC185_implies_long (G : Type*) [Magma G] (h : ConjunctionClass185 G) : ConjunctionClass185_long G := by
  obtain ⟨eq4287, eq4512⟩ := h
  have eq1 := Equation4287_4512_implies_Equation1 G eq4287 eq4512
  have eq4269 := Equation4287_4512_implies_Equation4269 G eq4287 eq4512
  have eq4284 := Equation4287_4512_implies_Equation4284 G eq4287 eq4512
  exact ⟨eq1, eq4269, eq4284, eq4287, eq4512⟩

theorem CC185_implied_by_long (G : Type*) [Magma G] : ConjunctionClass185_long G -> ConjunctionClass185 G :=
fun ⟨_, _, _, h4287, h4512⟩ => ⟨h4287, h4512⟩

theorem CC185_equiv (G : Type*) [Magma G] : ConjunctionClass185 G <-> ConjunctionClass185_long G :=
Iff.intro (CC185_implies_long G) (CC185_implied_by_long G)

theorem CC186_implies_long (G : Type*) [Magma G] (h : ConjunctionClass186 G) : ConjunctionClass186_long G := by
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

theorem CC186_implied_by_long (G : Type*) [Magma G] : ConjunctionClass186_long G -> ConjunctionClass186 G :=
fun ⟨_, h307, _, _, _, _, _, _, _, _, h4287, h4512⟩ => ⟨h307, h4287, h4512⟩

theorem CC186_equiv (G : Type*) [Magma G] : ConjunctionClass186 G <-> ConjunctionClass186_long G :=
Iff.intro (CC186_implies_long G) (CC186_implied_by_long G)

theorem CC187_implies_long (G : Type*) [Magma G] (h : ConjunctionClass187 G) : ConjunctionClass187_long G := by
  obtain ⟨eq4290, eq4512⟩ := h
  have eq1 := Equation4290_4512_implies_Equation1 G eq4290 eq4512
  exact ⟨eq1, eq4290, eq4512⟩

theorem CC187_implied_by_long (G : Type*) [Magma G] : ConjunctionClass187_long G -> ConjunctionClass187 G :=
fun ⟨_, h4290, h4512⟩ => ⟨h4290, h4512⟩

theorem CC187_equiv (G : Type*) [Magma G] : ConjunctionClass187 G <-> ConjunctionClass187_long G :=
Iff.intro (CC187_implies_long G) (CC187_implied_by_long G)

theorem CC188_implies_long (G : Type*) [Magma G] (h : ConjunctionClass188 G) : ConjunctionClass188_long G := by
  obtain ⟨eq307, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4290, eq4512⟩

theorem CC188_implied_by_long (G : Type*) [Magma G] : ConjunctionClass188_long G -> ConjunctionClass188 G :=
fun ⟨_, h307, _, h4290, h4512⟩ => ⟨h307, h4290, h4512⟩

theorem CC188_equiv (G : Type*) [Magma G] : ConjunctionClass188 G <-> ConjunctionClass188_long G :=
Iff.intro (CC188_implies_long G) (CC188_implied_by_long G)

theorem CC189_implies_long (G : Type*) [Magma G] (h : ConjunctionClass189 G) : ConjunctionClass189_long G := by
  obtain ⟨eq411, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq411, eq4290, eq4512⟩

theorem CC189_implied_by_long (G : Type*) [Magma G] : ConjunctionClass189_long G -> ConjunctionClass189 G :=
fun ⟨_, h411, h4290, h4512⟩ => ⟨h411, h4290, h4512⟩

theorem CC189_equiv (G : Type*) [Magma G] : ConjunctionClass189 G <-> ConjunctionClass189_long G :=
Iff.intro (CC189_implies_long G) (CC189_implied_by_long G)

theorem CC190_implies_long (G : Type*) [Magma G] (h : ConjunctionClass190 G) : ConjunctionClass190_long G := by
  obtain ⟨eq3253, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq3253, eq4290, eq4512⟩

theorem CC190_implied_by_long (G : Type*) [Magma G] : ConjunctionClass190_long G -> ConjunctionClass190 G :=
fun ⟨_, h3253, h4290, h4512⟩ => ⟨h3253, h4290, h4512⟩

theorem CC190_equiv (G : Type*) [Magma G] : ConjunctionClass190 G <-> ConjunctionClass190_long G :=
Iff.intro (CC190_implies_long G) (CC190_implied_by_long G)

theorem CC191_implies_long (G : Type*) [Magma G] (h : ConjunctionClass191 G) : ConjunctionClass191_long G := by
  obtain ⟨eq4269, eq4290, eq4512⟩ := h
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4290, eq4321, eq4512⟩

theorem CC191_implied_by_long (G : Type*) [Magma G] : ConjunctionClass191_long G -> ConjunctionClass191 G :=
fun ⟨_, h4269, _, _, _, h4290, _, h4512⟩ => ⟨h4269, h4290, h4512⟩

theorem CC191_equiv (G : Type*) [Magma G] : ConjunctionClass191 G <-> ConjunctionClass191_long G :=
Iff.intro (CC191_implies_long G) (CC191_implied_by_long G)

theorem CC192_implies_long (G : Type*) [Magma G] (h : ConjunctionClass192 G) : ConjunctionClass192_long G := by
  obtain ⟨eq4273, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4273, eq4290, eq4512⟩

theorem CC192_implied_by_long (G : Type*) [Magma G] : ConjunctionClass192_long G -> ConjunctionClass192 G :=
fun ⟨_, h4273, h4290, h4512⟩ => ⟨h4273, h4290, h4512⟩

theorem CC192_equiv (G : Type*) [Magma G] : ConjunctionClass192 G <-> ConjunctionClass192_long G :=
Iff.intro (CC192_implies_long G) (CC192_implied_by_long G)

theorem CC193_implies_long (G : Type*) [Magma G] (h : ConjunctionClass193 G) : ConjunctionClass193_long G := by
  obtain ⟨eq4276, eq4290, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4290, eq4512⟩

theorem CC193_implied_by_long (G : Type*) [Magma G] : ConjunctionClass193_long G -> ConjunctionClass193 G :=
fun ⟨_, h4276, h4290, h4512⟩ => ⟨h4276, h4290, h4512⟩

theorem CC193_equiv (G : Type*) [Magma G] : ConjunctionClass193 G <-> ConjunctionClass193_long G :=
Iff.intro (CC193_implies_long G) (CC193_implied_by_long G)

theorem CC194_implies_long (G : Type*) [Magma G] (h : ConjunctionClass194 G) : ConjunctionClass194_long G := by
  obtain ⟨eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4512⟩

theorem CC194_implied_by_long (G : Type*) [Magma G] : ConjunctionClass194_long G -> ConjunctionClass194 G :=
fun ⟨_, h4283, h4290, _, h4512⟩ => ⟨h4283, h4290, h4512⟩

theorem CC194_equiv (G : Type*) [Magma G] : ConjunctionClass194 G <-> ConjunctionClass194_long G :=
Iff.intro (CC194_implies_long G) (CC194_implied_by_long G)

theorem CC195_implies_long (G : Type*) [Magma G] (h : ConjunctionClass195 G) : ConjunctionClass195_long G := by
  obtain ⟨eq307, eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4512⟩

theorem CC195_implied_by_long (G : Type*) [Magma G] : ConjunctionClass195_long G -> ConjunctionClass195 G :=
fun ⟨_, h307, _, h4283, h4290, _, h4512⟩ => ⟨h307, h4283, h4290, h4512⟩

theorem CC195_equiv (G : Type*) [Magma G] : ConjunctionClass195 G <-> ConjunctionClass195_long G :=
Iff.intro (CC195_implies_long G) (CC195_implied_by_long G)

theorem CC196_implies_long (G : Type*) [Magma G] (h : ConjunctionClass196 G) : ConjunctionClass196_long G := by
  obtain ⟨eq3253, eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4512⟩

theorem CC196_implied_by_long (G : Type*) [Magma G] : ConjunctionClass196_long G -> ConjunctionClass196 G :=
fun ⟨_, h3253, h4283, h4290, _, h4512⟩ => ⟨h3253, h4283, h4290, h4512⟩

theorem CC196_equiv (G : Type*) [Magma G] : ConjunctionClass196 G <-> ConjunctionClass196_long G :=
Iff.intro (CC196_implies_long G) (CC196_implied_by_long G)

theorem CC197_implies_long (G : Type*) [Magma G] (h : ConjunctionClass197 G) : ConjunctionClass197_long G := by
  obtain ⟨eq4276, eq4283, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4512⟩

theorem CC197_implied_by_long (G : Type*) [Magma G] : ConjunctionClass197_long G -> ConjunctionClass197 G :=
fun ⟨_, h4276, h4283, h4290, _, h4512⟩ => ⟨h4276, h4283, h4290, h4512⟩

theorem CC197_equiv (G : Type*) [Magma G] : ConjunctionClass197 G <-> ConjunctionClass197_long G :=
Iff.intro (CC197_implies_long G) (CC197_implied_by_long G)

theorem CC198_implies_long (G : Type*) [Magma G] (h : ConjunctionClass198 G) : ConjunctionClass198_long G := by
  obtain ⟨eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4343, eq4512⟩

theorem CC198_implied_by_long (G : Type*) [Magma G] : ConjunctionClass198_long G -> ConjunctionClass198 G :=
fun ⟨_, h4284, h4290, _, _, h4512⟩ => ⟨h4284, h4290, h4512⟩

theorem CC198_equiv (G : Type*) [Magma G] : ConjunctionClass198 G <-> ConjunctionClass198_long G :=
Iff.intro (CC198_implies_long G) (CC198_implied_by_long G)

theorem CC199_implies_long (G : Type*) [Magma G] (h : ConjunctionClass199 G) : ConjunctionClass199_long G := by
  obtain ⟨eq307, eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4343, eq4512⟩

theorem CC199_implied_by_long (G : Type*) [Magma G] : ConjunctionClass199_long G -> ConjunctionClass199 G :=
fun ⟨_, h307, _, h4284, h4290, _, _, h4512⟩ => ⟨h307, h4284, h4290, h4512⟩

theorem CC199_equiv (G : Type*) [Magma G] : ConjunctionClass199 G <-> ConjunctionClass199_long G :=
Iff.intro (CC199_implies_long G) (CC199_implied_by_long G)

theorem CC200_implies_long (G : Type*) [Magma G] (h : ConjunctionClass200 G) : ConjunctionClass200_long G := by
  obtain ⟨eq4269, eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem CC200_implied_by_long (G : Type*) [Magma G] : ConjunctionClass200_long G -> ConjunctionClass200 G :=
fun ⟨_, h4269, _, _, _, h4284, h4290, _, _, _, h4512⟩ => ⟨h4269, h4284, h4290, h4512⟩

theorem CC200_equiv (G : Type*) [Magma G] : ConjunctionClass200 G <-> ConjunctionClass200_long G :=
Iff.intro (CC200_implies_long G) (CC200_implied_by_long G)

theorem CC201_implies_long (G : Type*) [Magma G] (h : ConjunctionClass201 G) : ConjunctionClass201_long G := by
  obtain ⟨eq4276, eq4284, eq4290, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4343, eq4512⟩

theorem CC201_implied_by_long (G : Type*) [Magma G] : ConjunctionClass201_long G -> ConjunctionClass201 G :=
fun ⟨_, h4276, h4284, h4290, _, _, h4512⟩ => ⟨h4276, h4284, h4290, h4512⟩

theorem CC201_equiv (G : Type*) [Magma G] : ConjunctionClass201 G <-> ConjunctionClass201_long G :=
Iff.intro (CC201_implies_long G) (CC201_implied_by_long G)

theorem CC202_implies_long (G : Type*) [Magma G] (h : ConjunctionClass202 G) : ConjunctionClass202_long G := by
  obtain ⟨eq4283, eq4284, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC202_implied_by_long (G : Type*) [Magma G] : ConjunctionClass202_long G -> ConjunctionClass202 G :=
fun ⟨_, h4283, h4284, h4290, _, _, _, _, _, _, h4512⟩ => ⟨h4283, h4284, h4290, h4512⟩

theorem CC202_equiv (G : Type*) [Magma G] : ConjunctionClass202 G <-> ConjunctionClass202_long G :=
Iff.intro (CC202_implies_long G) (CC202_implied_by_long G)

theorem CC203_implies_long (G : Type*) [Magma G] (h : ConjunctionClass203 G) : ConjunctionClass203_long G := by
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

theorem CC203_implied_by_long (G : Type*) [Magma G] : ConjunctionClass203_long G -> ConjunctionClass203 G :=
fun ⟨_, h307, _, h4283, h4284, h4290, _, _, _, _, _, _, h4512⟩ => ⟨h307, h4283, h4284, h4290, h4512⟩

theorem CC203_equiv (G : Type*) [Magma G] : ConjunctionClass203 G <-> ConjunctionClass203_long G :=
Iff.intro (CC203_implies_long G) (CC203_implied_by_long G)

theorem CC204_implies_long (G : Type*) [Magma G] (h : ConjunctionClass204 G) : ConjunctionClass204_long G := by
  obtain ⟨eq4276, eq4283, eq4284, eq4290, eq4512⟩ := h
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4291 := Equation4290_4314_4512_implies_Equation4291 G eq4290 eq4314 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4290, eq4291, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC204_implied_by_long (G : Type*) [Magma G] : ConjunctionClass204_long G -> ConjunctionClass204 G :=
fun ⟨_, h4276, h4283, h4284, h4290, _, _, _, _, _, _, h4512⟩ => ⟨h4276, h4283, h4284, h4290, h4512⟩

theorem CC204_equiv (G : Type*) [Magma G] : ConjunctionClass204 G <-> ConjunctionClass204_long G :=
Iff.intro (CC204_implies_long G) (CC204_implied_by_long G)

theorem CC205_implies_long (G : Type*) [Magma G] (h : ConjunctionClass205 G) : ConjunctionClass205_long G := by
  obtain ⟨eq4291, eq4512⟩ := h
  have eq1 := Equation4291_4512_implies_Equation1 G eq4291 eq4512
  exact ⟨eq1, eq4291, eq4512⟩

theorem CC205_implied_by_long (G : Type*) [Magma G] : ConjunctionClass205_long G -> ConjunctionClass205 G :=
fun ⟨_, h4291, h4512⟩ => ⟨h4291, h4512⟩

theorem CC205_equiv (G : Type*) [Magma G] : ConjunctionClass205 G <-> ConjunctionClass205_long G :=
Iff.intro (CC205_implies_long G) (CC205_implied_by_long G)

theorem CC206_implies_long (G : Type*) [Magma G] (h : ConjunctionClass206 G) : ConjunctionClass206_long G := by
  obtain ⟨eq307, eq4291, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4291, eq4512⟩

theorem CC206_implied_by_long (G : Type*) [Magma G] : ConjunctionClass206_long G -> ConjunctionClass206 G :=
fun ⟨_, h307, _, h4291, h4512⟩ => ⟨h307, h4291, h4512⟩

theorem CC206_equiv (G : Type*) [Magma G] : ConjunctionClass206 G <-> ConjunctionClass206_long G :=
Iff.intro (CC206_implies_long G) (CC206_implied_by_long G)

theorem CC207_implies_long (G : Type*) [Magma G] (h : ConjunctionClass207 G) : ConjunctionClass207_long G := by
  obtain ⟨eq312, eq4291, eq4512⟩ := h
  have eq1 := Equation312_4512_implies_Equation1 G eq312 eq4512
  have eq307 := Equation312_4512_implies_Equation307 G eq312 eq4512
  have eq3253 := Equation312_4512_implies_Equation3253 G eq312 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  have eq4272 := Equation312_4512_implies_Equation4272 G eq312 eq4512
  exact ⟨eq1, eq307, eq312, eq3253, eq3258, eq3278, eq4272, eq4291, eq4512⟩

theorem CC207_implied_by_long (G : Type*) [Magma G] : ConjunctionClass207_long G -> ConjunctionClass207 G :=
fun ⟨_, _, h312, _, _, _, _, h4291, h4512⟩ => ⟨h312, h4291, h4512⟩

theorem CC207_equiv (G : Type*) [Magma G] : ConjunctionClass207 G <-> ConjunctionClass207_long G :=
Iff.intro (CC207_implies_long G) (CC207_implied_by_long G)

theorem CC208_implies_long (G : Type*) [Magma G] (h : ConjunctionClass208 G) : ConjunctionClass208_long G := by
  obtain ⟨eq326, eq4291, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4291, eq4512⟩

theorem CC208_implied_by_long (G : Type*) [Magma G] : ConjunctionClass208_long G -> ConjunctionClass208 G :=
fun ⟨_, _, h326, _, _, h4291, h4512⟩ => ⟨h326, h4291, h4512⟩

theorem CC208_equiv (G : Type*) [Magma G] : ConjunctionClass208 G <-> ConjunctionClass208_long G :=
Iff.intro (CC208_implies_long G) (CC208_implied_by_long G)

theorem CC209_implies_long (G : Type*) [Magma G] (h : ConjunctionClass209 G) : ConjunctionClass209_long G := by
  obtain ⟨eq4270, eq4291, eq4512⟩ := h
  have eq4272 := Equation4270_4291_4512_implies_Equation4272 G eq4270 eq4291 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4291, eq4343, eq4512⟩

theorem CC209_implied_by_long (G : Type*) [Magma G] : ConjunctionClass209_long G -> ConjunctionClass209 G :=
fun ⟨_, h4270, _, _, _, h4291, _, h4512⟩ => ⟨h4270, h4291, h4512⟩

theorem CC209_equiv (G : Type*) [Magma G] : ConjunctionClass209 G <-> ConjunctionClass209_long G :=
Iff.intro (CC209_implies_long G) (CC209_implied_by_long G)

theorem CC210_implies_long (G : Type*) [Magma G] (h : ConjunctionClass210 G) : ConjunctionClass210_long G := by
  obtain ⟨eq4272, eq4291, eq4512⟩ := h
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  exact ⟨eq1, eq4272, eq4291, eq4512⟩

theorem CC210_implied_by_long (G : Type*) [Magma G] : ConjunctionClass210_long G -> ConjunctionClass210 G :=
fun ⟨_, h4272, h4291, h4512⟩ => ⟨h4272, h4291, h4512⟩

theorem CC210_equiv (G : Type*) [Magma G] : ConjunctionClass210 G <-> ConjunctionClass210_long G :=
Iff.intro (CC210_implies_long G) (CC210_implied_by_long G)

theorem CC211_implies_long (G : Type*) [Magma G] (h : ConjunctionClass211 G) : ConjunctionClass211_long G := by
  obtain ⟨eq4276, eq4291, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4291, eq4512⟩

theorem CC211_implied_by_long (G : Type*) [Magma G] : ConjunctionClass211_long G -> ConjunctionClass211 G :=
fun ⟨_, h4276, h4291, h4512⟩ => ⟨h4276, h4291, h4512⟩

theorem CC211_equiv (G : Type*) [Magma G] : ConjunctionClass211 G <-> ConjunctionClass211_long G :=
Iff.intro (CC211_implies_long G) (CC211_implied_by_long G)

theorem CC212_implies_long (G : Type*) [Magma G] (h : ConjunctionClass212 G) : ConjunctionClass212_long G := by
  obtain ⟨eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4512⟩

theorem CC212_implied_by_long (G : Type*) [Magma G] : ConjunctionClass212_long G -> ConjunctionClass212 G :=
fun ⟨_, h4283, h4291, _, _, h4512⟩ => ⟨h4283, h4291, h4512⟩

theorem CC212_equiv (G : Type*) [Magma G] : ConjunctionClass212 G <-> ConjunctionClass212_long G :=
Iff.intro (CC212_implies_long G) (CC212_implied_by_long G)

theorem CC213_implies_long (G : Type*) [Magma G] (h : ConjunctionClass213 G) : ConjunctionClass213_long G := by
  obtain ⟨eq307, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4291, eq4293, eq4321, eq4512⟩

theorem CC213_implied_by_long (G : Type*) [Magma G] : ConjunctionClass213_long G -> ConjunctionClass213 G :=
fun ⟨_, h307, _, h4283, h4291, _, _, h4512⟩ => ⟨h307, h4283, h4291, h4512⟩

theorem CC213_equiv (G : Type*) [Magma G] : ConjunctionClass213 G <-> ConjunctionClass213_long G :=
Iff.intro (CC213_implies_long G) (CC213_implied_by_long G)

theorem CC214_implies_long (G : Type*) [Magma G] (h : ConjunctionClass214 G) : ConjunctionClass214_long G := by
  obtain ⟨eq326, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4291_4512_implies_Equation1 G eq4291 eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  have eq4358 := Equation326_4293_4512_implies_Equation4358 G eq326 eq4293 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem CC214_implied_by_long (G : Type*) [Magma G] : ConjunctionClass214_long G -> ConjunctionClass214 G :=
fun ⟨_, _, h326, _, _, h4283, h4291, _, _, _, h4512⟩ => ⟨h326, h4283, h4291, h4512⟩

theorem CC214_equiv (G : Type*) [Magma G] : ConjunctionClass214 G <-> ConjunctionClass214_long G :=
Iff.intro (CC214_implies_long G) (CC214_implied_by_long G)

theorem CC215_implies_long (G : Type*) [Magma G] (h : ConjunctionClass215 G) : ConjunctionClass215_long G := by
  obtain ⟨eq4270, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq4272 := Equation4270_4291_4512_implies_Equation4272 G eq4270 eq4291 eq4512
  have eq1 := Equation4291_4512_implies_Equation1 G eq4291 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4291, eq4293, eq4321, eq4343, eq4512⟩

theorem CC215_implied_by_long (G : Type*) [Magma G] : ConjunctionClass215_long G -> ConjunctionClass215 G :=
fun ⟨_, h4270, _, _, _, h4283, h4291, _, _, _, h4512⟩ => ⟨h4270, h4283, h4291, h4512⟩

theorem CC215_equiv (G : Type*) [Magma G] : ConjunctionClass215 G <-> ConjunctionClass215_long G :=
Iff.intro (CC215_implies_long G) (CC215_implied_by_long G)

theorem CC216_implies_long (G : Type*) [Magma G] (h : ConjunctionClass216 G) : ConjunctionClass216_long G := by
  obtain ⟨eq4276, eq4283, eq4291, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4512⟩

theorem CC216_implied_by_long (G : Type*) [Magma G] : ConjunctionClass216_long G -> ConjunctionClass216 G :=
fun ⟨_, h4276, h4283, h4291, _, _, h4512⟩ => ⟨h4276, h4283, h4291, h4512⟩

theorem CC216_equiv (G : Type*) [Magma G] : ConjunctionClass216 G <-> ConjunctionClass216_long G :=
Iff.intro (CC216_implies_long G) (CC216_implied_by_long G)

theorem CC217_implies_long (G : Type*) [Magma G] (h : ConjunctionClass217 G) : ConjunctionClass217_long G := by
  obtain ⟨eq4284, eq4291, eq4512⟩ := h
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4291, eq4320, eq4512⟩

theorem CC217_implied_by_long (G : Type*) [Magma G] : ConjunctionClass217_long G -> ConjunctionClass217 G :=
fun ⟨_, h4284, h4291, _, h4512⟩ => ⟨h4284, h4291, h4512⟩

theorem CC217_equiv (G : Type*) [Magma G] : ConjunctionClass217 G <-> ConjunctionClass217_long G :=
Iff.intro (CC217_implies_long G) (CC217_implied_by_long G)

theorem CC218_implies_long (G : Type*) [Magma G] (h : ConjunctionClass218 G) : ConjunctionClass218_long G := by
  obtain ⟨eq307, eq4284, eq4291, eq4512⟩ := h
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4291, eq4320, eq4512⟩

theorem CC218_implied_by_long (G : Type*) [Magma G] : ConjunctionClass218_long G -> ConjunctionClass218 G :=
fun ⟨_, h307, _, h4284, h4291, _, h4512⟩ => ⟨h307, h4284, h4291, h4512⟩

theorem CC218_equiv (G : Type*) [Magma G] : ConjunctionClass218 G <-> ConjunctionClass218_long G :=
Iff.intro (CC218_implies_long G) (CC218_implied_by_long G)

theorem CC219_implies_long (G : Type*) [Magma G] (h : ConjunctionClass219 G) : ConjunctionClass219_long G := by
  obtain ⟨eq4276, eq4284, eq4291, eq4512⟩ := h
  have eq4320 := Equation4284_4291_4512_implies_Equation4320 G eq4284 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4291, eq4320, eq4512⟩

theorem CC219_implied_by_long (G : Type*) [Magma G] : ConjunctionClass219_long G -> ConjunctionClass219 G :=
fun ⟨_, h4276, h4284, h4291, _, h4512⟩ => ⟨h4276, h4284, h4291, h4512⟩

theorem CC219_equiv (G : Type*) [Magma G] : ConjunctionClass219 G <-> ConjunctionClass219_long G :=
Iff.intro (CC219_implies_long G) (CC219_implied_by_long G)

theorem CC220_implies_long (G : Type*) [Magma G] (h : ConjunctionClass220 G) : ConjunctionClass220_long G := by
  obtain ⟨eq4290, eq4291, eq4512⟩ := h
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4290, eq4291, eq4314, eq4512⟩

theorem CC220_implied_by_long (G : Type*) [Magma G] : ConjunctionClass220_long G -> ConjunctionClass220 G :=
fun ⟨_, h4290, h4291, _, h4512⟩ => ⟨h4290, h4291, h4512⟩

theorem CC220_equiv (G : Type*) [Magma G] : ConjunctionClass220 G <-> ConjunctionClass220_long G :=
Iff.intro (CC220_implies_long G) (CC220_implied_by_long G)

theorem CC221_implies_long (G : Type*) [Magma G] (h : ConjunctionClass221 G) : ConjunctionClass221_long G := by
  obtain ⟨eq4276, eq4290, eq4291, eq4512⟩ := h
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4290, eq4291, eq4314, eq4512⟩

theorem CC221_implied_by_long (G : Type*) [Magma G] : ConjunctionClass221_long G -> ConjunctionClass221 G :=
fun ⟨_, h4276, h4290, h4291, _, h4512⟩ => ⟨h4276, h4290, h4291, h4512⟩

theorem CC221_equiv (G : Type*) [Magma G] : ConjunctionClass221 G <-> ConjunctionClass221_long G :=
Iff.intro (CC221_implies_long G) (CC221_implied_by_long G)

theorem CC222_implies_long (G : Type*) [Magma G] (h : ConjunctionClass222 G) : ConjunctionClass222_long G := by
  obtain ⟨eq4293, eq4512⟩ := h
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  exact ⟨eq1, eq4293, eq4512⟩

theorem CC222_implied_by_long (G : Type*) [Magma G] : ConjunctionClass222_long G -> ConjunctionClass222 G :=
fun ⟨_, h4293, h4512⟩ => ⟨h4293, h4512⟩

theorem CC222_equiv (G : Type*) [Magma G] : ConjunctionClass222 G <-> ConjunctionClass222_long G :=
Iff.intro (CC222_implies_long G) (CC222_implied_by_long G)

theorem CC223_implies_long (G : Type*) [Magma G] (h : ConjunctionClass223 G) : ConjunctionClass223_long G := by
  obtain ⟨eq307, eq4293, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4293, eq4512⟩

theorem CC223_implied_by_long (G : Type*) [Magma G] : ConjunctionClass223_long G -> ConjunctionClass223 G :=
fun ⟨_, h307, _, h4293, h4512⟩ => ⟨h307, h4293, h4512⟩

theorem CC223_equiv (G : Type*) [Magma G] : ConjunctionClass223 G <-> ConjunctionClass223_long G :=
Iff.intro (CC223_implies_long G) (CC223_implied_by_long G)

theorem CC224_implies_long (G : Type*) [Magma G] (h : ConjunctionClass224 G) : ConjunctionClass224_long G := by
  obtain ⟨eq4269, eq4293, eq4512⟩ := h
  have eq4273 := Equation4269_4293_4512_implies_Equation4273 G eq4269 eq4293 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4293, eq4321, eq4512⟩

theorem CC224_implied_by_long (G : Type*) [Magma G] : ConjunctionClass224_long G -> ConjunctionClass224 G :=
fun ⟨_, h4269, _, _, _, h4293, _, h4512⟩ => ⟨h4269, h4293, h4512⟩

theorem CC224_equiv (G : Type*) [Magma G] : ConjunctionClass224 G <-> ConjunctionClass224_long G :=
Iff.intro (CC224_implies_long G) (CC224_implied_by_long G)

theorem CC225_implies_long (G : Type*) [Magma G] (h : ConjunctionClass225 G) : ConjunctionClass225_long G := by
  obtain ⟨eq4270, eq4293, eq4512⟩ := h
  have eq4272 := Equation4270_4293_4512_implies_Equation4272 G eq4270 eq4293 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4293, eq4343, eq4512⟩

theorem CC225_implied_by_long (G : Type*) [Magma G] : ConjunctionClass225_long G -> ConjunctionClass225 G :=
fun ⟨_, h4270, _, _, _, h4293, _, h4512⟩ => ⟨h4270, h4293, h4512⟩

theorem CC225_equiv (G : Type*) [Magma G] : ConjunctionClass225 G <-> ConjunctionClass225_long G :=
Iff.intro (CC225_implies_long G) (CC225_implied_by_long G)

theorem CC226_implies_long (G : Type*) [Magma G] (h : ConjunctionClass226 G) : ConjunctionClass226_long G := by
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

theorem CC226_implied_by_long (G : Type*) [Magma G] : ConjunctionClass226_long G -> ConjunctionClass226 G :=
fun ⟨_, h4269, h4270, _, _, _, _, _, h4293, _, _, _, _, _, _, _, _, h4512⟩ => ⟨h4269, h4270, h4293, h4512⟩

theorem CC226_equiv (G : Type*) [Magma G] : ConjunctionClass226 G <-> ConjunctionClass226_long G :=
Iff.intro (CC226_implies_long G) (CC226_implied_by_long G)

theorem CC227_implies_long (G : Type*) [Magma G] (h : ConjunctionClass227 G) : ConjunctionClass227_long G := by
  obtain ⟨eq4276, eq4293, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4512⟩

theorem CC227_implied_by_long (G : Type*) [Magma G] : ConjunctionClass227_long G -> ConjunctionClass227 G :=
fun ⟨_, h4276, h4293, h4512⟩ => ⟨h4276, h4293, h4512⟩

theorem CC227_equiv (G : Type*) [Magma G] : ConjunctionClass227 G <-> ConjunctionClass227_long G :=
Iff.intro (CC227_implies_long G) (CC227_implied_by_long G)

theorem CC228_implies_long (G : Type*) [Magma G] (h : ConjunctionClass228 G) : ConjunctionClass228_long G := by
  obtain ⟨eq4300, eq4512⟩ := h
  have eq1 := Equation4300_4512_implies_Equation1 G eq4300 eq4512
  have eq4272 := Equation4300_4512_implies_Equation4272 G eq4300 eq4512
  have eq4291 := Equation4300_4512_implies_Equation4291 G eq4300 eq4512
  exact ⟨eq1, eq4272, eq4291, eq4300, eq4512⟩

theorem CC228_implied_by_long (G : Type*) [Magma G] : ConjunctionClass228_long G -> ConjunctionClass228 G :=
fun ⟨_, _, _, h4300, h4512⟩ => ⟨h4300, h4512⟩

theorem CC228_equiv (G : Type*) [Magma G] : ConjunctionClass228 G <-> ConjunctionClass228_long G :=
Iff.intro (CC228_implies_long G) (CC228_implied_by_long G)

theorem CC229_implies_long (G : Type*) [Magma G] (h : ConjunctionClass229 G) : ConjunctionClass229_long G := by
  obtain ⟨eq307, eq4300, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4272 := Equation4300_4512_implies_Equation4272 G eq4300 eq4512
  have eq4291 := Equation4300_4512_implies_Equation4291 G eq4300 eq4512
  have eq312 := Equation307_4272_4512_implies_Equation312 G eq307 eq4272 eq4512
  have eq3258 := Equation312_4512_implies_Equation3258 G eq312 eq4512
  have eq3278 := Equation312_4512_implies_Equation3278 G eq312 eq4512
  exact ⟨eq1, eq307, eq312, eq3253, eq3258, eq3278, eq4272, eq4291, eq4300, eq4512⟩

theorem CC229_implied_by_long (G : Type*) [Magma G] : ConjunctionClass229_long G -> ConjunctionClass229 G :=
fun ⟨_, h307, _, _, _, _, _, _, h4300, h4512⟩ => ⟨h307, h4300, h4512⟩

theorem CC229_equiv (G : Type*) [Magma G] : ConjunctionClass229 G <-> ConjunctionClass229_long G :=
Iff.intro (CC229_implies_long G) (CC229_implied_by_long G)

theorem CC230_implies_long (G : Type*) [Magma G] (h : ConjunctionClass230 G) : ConjunctionClass230_long G := by
  obtain ⟨eq4314, eq4512⟩ := h
  have eq1 := Equation4314_4512_implies_Equation1 G eq4314 eq4512
  exact ⟨eq1, eq4314, eq4512⟩

theorem CC230_implied_by_long (G : Type*) [Magma G] : ConjunctionClass230_long G -> ConjunctionClass230 G :=
fun ⟨_, h4314, h4512⟩ => ⟨h4314, h4512⟩

theorem CC230_equiv (G : Type*) [Magma G] : ConjunctionClass230 G <-> ConjunctionClass230_long G :=
Iff.intro (CC230_implies_long G) (CC230_implied_by_long G)

theorem CC231_implies_long (G : Type*) [Magma G] (h : ConjunctionClass231 G) : ConjunctionClass231_long G := by
  obtain ⟨eq307, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4314, eq4512⟩

theorem CC231_implied_by_long (G : Type*) [Magma G] : ConjunctionClass231_long G -> ConjunctionClass231 G :=
fun ⟨_, h307, _, h4314, h4512⟩ => ⟨h307, h4314, h4512⟩

theorem CC231_equiv (G : Type*) [Magma G] : ConjunctionClass231 G <-> ConjunctionClass231_long G :=
Iff.intro (CC231_implies_long G) (CC231_implied_by_long G)

theorem CC232_implies_long (G : Type*) [Magma G] (h : ConjunctionClass232 G) : ConjunctionClass232_long G := by
  obtain ⟨eq308, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation308_4512_implies_Equation307 G eq308 eq4512
  have eq3253 := Equation308_4512_implies_Equation3253 G eq308 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  have eq4268 := Equation308_4512_implies_Equation4268 G eq308 eq4512
  exact ⟨eq1, eq307, eq308, eq3253, eq3255, eq3256, eq4268, eq4314, eq4512⟩

theorem CC232_implied_by_long (G : Type*) [Magma G] : ConjunctionClass232_long G -> ConjunctionClass232 G :=
fun ⟨_, _, h308, _, _, _, _, h4314, h4512⟩ => ⟨h308, h4314, h4512⟩

theorem CC232_equiv (G : Type*) [Magma G] : ConjunctionClass232 G <-> ConjunctionClass232_long G :=
Iff.intro (CC232_implies_long G) (CC232_implied_by_long G)

theorem CC233_implies_long (G : Type*) [Magma G] (h : ConjunctionClass233 G) : ConjunctionClass233_long G := by
  obtain ⟨eq323, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4314, eq4512⟩

theorem CC233_implied_by_long (G : Type*) [Magma G] : ConjunctionClass233_long G -> ConjunctionClass233 G :=
fun ⟨_, _, h323, _, _, h4314, h4512⟩ => ⟨h323, h4314, h4512⟩

theorem CC233_equiv (G : Type*) [Magma G] : ConjunctionClass233 G <-> ConjunctionClass233_long G :=
Iff.intro (CC233_implies_long G) (CC233_implied_by_long G)

theorem CC234_implies_long (G : Type*) [Magma G] (h : ConjunctionClass234 G) : ConjunctionClass234_long G := by
  obtain ⟨eq4268, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4268, eq4314, eq4512⟩

theorem CC234_implied_by_long (G : Type*) [Magma G] : ConjunctionClass234_long G -> ConjunctionClass234 G :=
fun ⟨_, h4268, h4314, h4512⟩ => ⟨h4268, h4314, h4512⟩

theorem CC234_equiv (G : Type*) [Magma G] : ConjunctionClass234 G <-> ConjunctionClass234_long G :=
Iff.intro (CC234_implies_long G) (CC234_implied_by_long G)

theorem CC235_implies_long (G : Type*) [Magma G] (h : ConjunctionClass235 G) : ConjunctionClass235_long G := by
  obtain ⟨eq4275, eq4314, eq4512⟩ := h
  have eq4268 := Equation4275_4314_4512_implies_Equation4268 G eq4275 eq4314 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4314, eq4512⟩

theorem CC235_implied_by_long (G : Type*) [Magma G] : ConjunctionClass235_long G -> ConjunctionClass235 G :=
fun ⟨_, _, h4275, _, _, _, h4314, h4512⟩ => ⟨h4275, h4314, h4512⟩

theorem CC235_equiv (G : Type*) [Magma G] : ConjunctionClass235 G <-> ConjunctionClass235_long G :=
Iff.intro (CC235_implies_long G) (CC235_implied_by_long G)

theorem CC236_implies_long (G : Type*) [Magma G] (h : ConjunctionClass236 G) : ConjunctionClass236_long G := by
  obtain ⟨eq4276, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4314, eq4512⟩

theorem CC236_implied_by_long (G : Type*) [Magma G] : ConjunctionClass236_long G -> ConjunctionClass236 G :=
fun ⟨_, h4276, h4314, h4512⟩ => ⟨h4276, h4314, h4512⟩

theorem CC236_equiv (G : Type*) [Magma G] : ConjunctionClass236 G <-> ConjunctionClass236_long G :=
Iff.intro (CC236_implies_long G) (CC236_implied_by_long G)

theorem CC237_implies_long (G : Type*) [Magma G] (h : ConjunctionClass237 G) : ConjunctionClass237_long G := by
  obtain ⟨eq4293, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4314, eq4512⟩

theorem CC237_implied_by_long (G : Type*) [Magma G] : ConjunctionClass237_long G -> ConjunctionClass237 G :=
fun ⟨_, h4293, h4314, h4512⟩ => ⟨h4293, h4314, h4512⟩

theorem CC237_equiv (G : Type*) [Magma G] : ConjunctionClass237 G <-> ConjunctionClass237_long G :=
Iff.intro (CC237_implies_long G) (CC237_implied_by_long G)

theorem CC238_implies_long (G : Type*) [Magma G] (h : ConjunctionClass238 G) : ConjunctionClass238_long G := by
  obtain ⟨eq4276, eq4293, eq4314, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4314, eq4512⟩

theorem CC238_implied_by_long (G : Type*) [Magma G] : ConjunctionClass238_long G -> ConjunctionClass238 G :=
fun ⟨_, h4276, h4293, h4314, h4512⟩ => ⟨h4276, h4293, h4314, h4512⟩

theorem CC238_equiv (G : Type*) [Magma G] : ConjunctionClass238 G <-> ConjunctionClass238_long G :=
Iff.intro (CC238_implies_long G) (CC238_implied_by_long G)

theorem CC239_implies_long (G : Type*) [Magma G] (h : ConjunctionClass239 G) : ConjunctionClass239_long G := by
  obtain ⟨eq4315, eq4512⟩ := h
  have eq1 := Equation4315_4512_implies_Equation1 G eq4315 eq4512
  have eq4268 := Equation4315_4512_implies_Equation4268 G eq4315 eq4512
  have eq4314 := Equation4315_4512_implies_Equation4314 G eq4315 eq4512
  exact ⟨eq1, eq4268, eq4314, eq4315, eq4512⟩

theorem CC239_implied_by_long (G : Type*) [Magma G] : ConjunctionClass239_long G -> ConjunctionClass239 G :=
fun ⟨_, _, _, h4315, h4512⟩ => ⟨h4315, h4512⟩

theorem CC239_equiv (G : Type*) [Magma G] : ConjunctionClass239 G <-> ConjunctionClass239_long G :=
Iff.intro (CC239_implies_long G) (CC239_implied_by_long G)

theorem CC240_implies_long (G : Type*) [Magma G] (h : ConjunctionClass240 G) : ConjunctionClass240_long G := by
  obtain ⟨eq307, eq4315, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4268 := Equation4315_4512_implies_Equation4268 G eq4315 eq4512
  have eq4314 := Equation4315_4512_implies_Equation4314 G eq4315 eq4512
  have eq308 := Equation307_4268_4512_implies_Equation308 G eq307 eq4268 eq4512
  have eq3255 := Equation308_4512_implies_Equation3255 G eq308 eq4512
  have eq3256 := Equation308_4512_implies_Equation3256 G eq308 eq4512
  exact ⟨eq1, eq307, eq308, eq3253, eq3255, eq3256, eq4268, eq4314, eq4315, eq4512⟩

theorem CC240_implied_by_long (G : Type*) [Magma G] : ConjunctionClass240_long G -> ConjunctionClass240 G :=
fun ⟨_, h307, _, _, _, _, _, _, h4315, h4512⟩ => ⟨h307, h4315, h4512⟩

theorem CC240_equiv (G : Type*) [Magma G] : ConjunctionClass240 G <-> ConjunctionClass240_long G :=
Iff.intro (CC240_implies_long G) (CC240_implied_by_long G)

theorem CC241_implies_long (G : Type*) [Magma G] (h : ConjunctionClass241 G) : ConjunctionClass241_long G := by
  obtain ⟨eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4320, eq4512⟩

theorem CC241_implied_by_long (G : Type*) [Magma G] : ConjunctionClass241_long G -> ConjunctionClass241 G :=
fun ⟨_, h4320, h4512⟩ => ⟨h4320, h4512⟩

theorem CC241_equiv (G : Type*) [Magma G] : ConjunctionClass241 G <-> ConjunctionClass241_long G :=
Iff.intro (CC241_implies_long G) (CC241_implied_by_long G)

theorem CC242_implies_long (G : Type*) [Magma G] (h : ConjunctionClass242 G) : ConjunctionClass242_long G := by
  obtain ⟨eq47, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq47, eq4320, eq4512⟩

theorem CC242_implied_by_long (G : Type*) [Magma G] : ConjunctionClass242_long G -> ConjunctionClass242 G :=
fun ⟨_, h47, h4320, h4512⟩ => ⟨h47, h4320, h4512⟩

theorem CC242_equiv (G : Type*) [Magma G] : ConjunctionClass242 G <-> ConjunctionClass242_long G :=
Iff.intro (CC242_implies_long G) (CC242_implied_by_long G)

theorem CC243_implies_long (G : Type*) [Magma G] (h : ConjunctionClass243 G) : ConjunctionClass243_long G := by
  obtain ⟨eq75, eq4320, eq4512⟩ := h
  have eq4362 := Equation75_4320_4512_implies_Equation4362 G eq75 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq47 := Equation75_4512_implies_Equation47 G eq75 eq4512
  exact ⟨eq1, eq47, eq75, eq4320, eq4362, eq4512⟩

theorem CC243_implied_by_long (G : Type*) [Magma G] : ConjunctionClass243_long G -> ConjunctionClass243 G :=
fun ⟨_, _, h75, h4320, _, h4512⟩ => ⟨h75, h4320, h4512⟩

theorem CC243_equiv (G : Type*) [Magma G] : ConjunctionClass243 G <-> ConjunctionClass243_long G :=
Iff.intro (CC243_implies_long G) (CC243_implied_by_long G)

theorem CC244_implies_long (G : Type*) [Magma G] (h : ConjunctionClass244 G) : ConjunctionClass244_long G := by
  obtain ⟨eq307, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4320, eq4512⟩

theorem CC244_implied_by_long (G : Type*) [Magma G] : ConjunctionClass244_long G -> ConjunctionClass244 G :=
fun ⟨_, h307, _, h4320, h4512⟩ => ⟨h307, h4320, h4512⟩

theorem CC244_equiv (G : Type*) [Magma G] : ConjunctionClass244 G <-> ConjunctionClass244_long G :=
Iff.intro (CC244_implies_long G) (CC244_implied_by_long G)

theorem CC245_implies_long (G : Type*) [Magma G] (h : ConjunctionClass245 G) : ConjunctionClass245_long G := by
  obtain ⟨eq323, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4320, eq4512⟩

theorem CC245_implied_by_long (G : Type*) [Magma G] : ConjunctionClass245_long G -> ConjunctionClass245 G :=
fun ⟨_, _, h323, _, _, h4320, h4512⟩ => ⟨h323, h4320, h4512⟩

theorem CC245_equiv (G : Type*) [Magma G] : ConjunctionClass245 G <-> ConjunctionClass245_long G :=
Iff.intro (CC245_implies_long G) (CC245_implied_by_long G)

theorem CC246_implies_long (G : Type*) [Magma G] (h : ConjunctionClass246 G) : ConjunctionClass246_long G := by
  obtain ⟨eq411, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq411, eq4320, eq4512⟩

theorem CC246_implied_by_long (G : Type*) [Magma G] : ConjunctionClass246_long G -> ConjunctionClass246 G :=
fun ⟨_, h411, h4320, h4512⟩ => ⟨h411, h4320, h4512⟩

theorem CC246_equiv (G : Type*) [Magma G] : ConjunctionClass246 G <-> ConjunctionClass246_long G :=
Iff.intro (CC246_implies_long G) (CC246_implied_by_long G)

theorem CC247_implies_long (G : Type*) [Magma G] (h : ConjunctionClass247 G) : ConjunctionClass247_long G := by
  obtain ⟨eq513, eq4320, eq4512⟩ := h
  have eq4362 := Equation513_4320_4512_implies_Equation4362 G eq513 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq411 := Equation513_4512_implies_Equation411 G eq513 eq4512
  exact ⟨eq1, eq411, eq513, eq4320, eq4362, eq4512⟩

theorem CC247_implied_by_long (G : Type*) [Magma G] : ConjunctionClass247_long G -> ConjunctionClass247 G :=
fun ⟨_, _, h513, h4320, _, h4512⟩ => ⟨h513, h4320, h4512⟩

theorem CC247_equiv (G : Type*) [Magma G] : ConjunctionClass247 G <-> ConjunctionClass247_long G :=
Iff.intro (CC247_implies_long G) (CC247_implied_by_long G)

theorem CC248_implies_long (G : Type*) [Magma G] (h : ConjunctionClass248 G) : ConjunctionClass248_long G := by
  obtain ⟨eq3253, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq3253, eq4320, eq4512⟩

theorem CC248_implied_by_long (G : Type*) [Magma G] : ConjunctionClass248_long G -> ConjunctionClass248 G :=
fun ⟨_, h3253, h4320, h4512⟩ => ⟨h3253, h4320, h4512⟩

theorem CC248_equiv (G : Type*) [Magma G] : ConjunctionClass248 G <-> ConjunctionClass248_long G :=
Iff.intro (CC248_implies_long G) (CC248_implied_by_long G)

theorem CC249_implies_long (G : Type*) [Magma G] (h : ConjunctionClass249 G) : ConjunctionClass249_long G := by
  obtain ⟨eq3261, eq4320, eq4512⟩ := h
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq4275, eq4320, eq4512⟩

theorem CC249_implied_by_long (G : Type*) [Magma G] : ConjunctionClass249_long G -> ConjunctionClass249 G :=
fun ⟨_, _, h3261, _, _, _, h4320, h4512⟩ => ⟨h3261, h4320, h4512⟩

theorem CC249_equiv (G : Type*) [Magma G] : ConjunctionClass249 G <-> ConjunctionClass249_long G :=
Iff.intro (CC249_implies_long G) (CC249_implied_by_long G)

theorem CC250_implies_long (G : Type*) [Magma G] (h : ConjunctionClass250 G) : ConjunctionClass250_long G := by
  obtain ⟨eq3306, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  exact ⟨eq1, eq3253, eq3306, eq4320, eq4512⟩

theorem CC250_implied_by_long (G : Type*) [Magma G] : ConjunctionClass250_long G -> ConjunctionClass250 G :=
fun ⟨_, _, h3306, h4320, h4512⟩ => ⟨h3306, h4320, h4512⟩

theorem CC250_equiv (G : Type*) [Magma G] : ConjunctionClass250 G <-> ConjunctionClass250_long G :=
Iff.intro (CC250_implies_long G) (CC250_implied_by_long G)

theorem CC251_implies_long (G : Type*) [Magma G] (h : ConjunctionClass251 G) : ConjunctionClass251_long G := by
  obtain ⟨eq4268, eq4320, eq4512⟩ := h
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4320, eq4512⟩

theorem CC251_implied_by_long (G : Type*) [Magma G] : ConjunctionClass251_long G -> ConjunctionClass251 G :=
fun ⟨_, h4268, _, _, _, _, h4320, h4512⟩ => ⟨h4268, h4320, h4512⟩

theorem CC251_equiv (G : Type*) [Magma G] : ConjunctionClass251 G <-> ConjunctionClass251_long G :=
Iff.intro (CC251_implies_long G) (CC251_implied_by_long G)

theorem CC252_implies_long (G : Type*) [Magma G] (h : ConjunctionClass252 G) : ConjunctionClass252_long G := by
  obtain ⟨eq4275, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4275, eq4320, eq4512⟩

theorem CC252_implied_by_long (G : Type*) [Magma G] : ConjunctionClass252_long G -> ConjunctionClass252 G :=
fun ⟨_, h4275, h4320, h4512⟩ => ⟨h4275, h4320, h4512⟩

theorem CC252_equiv (G : Type*) [Magma G] : ConjunctionClass252 G <-> ConjunctionClass252_long G :=
Iff.intro (CC252_implies_long G) (CC252_implied_by_long G)

theorem CC253_implies_long (G : Type*) [Magma G] (h : ConjunctionClass253 G) : ConjunctionClass253_long G := by
  obtain ⟨eq4276, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4320, eq4512⟩

theorem CC253_implied_by_long (G : Type*) [Magma G] : ConjunctionClass253_long G -> ConjunctionClass253 G :=
fun ⟨_, h4276, h4320, h4512⟩ => ⟨h4276, h4320, h4512⟩

theorem CC253_equiv (G : Type*) [Magma G] : ConjunctionClass253 G <-> ConjunctionClass253_long G :=
Iff.intro (CC253_implies_long G) (CC253_implied_by_long G)

theorem CC254_implies_long (G : Type*) [Magma G] (h : ConjunctionClass254 G) : ConjunctionClass254_long G := by
  obtain ⟨eq4293, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4293, eq4320, eq4512⟩

theorem CC254_implied_by_long (G : Type*) [Magma G] : ConjunctionClass254_long G -> ConjunctionClass254 G :=
fun ⟨_, h4293, h4320, h4512⟩ => ⟨h4293, h4320, h4512⟩

theorem CC254_equiv (G : Type*) [Magma G] : ConjunctionClass254 G <-> ConjunctionClass254_long G :=
Iff.intro (CC254_implies_long G) (CC254_implied_by_long G)

theorem CC255_implies_long (G : Type*) [Magma G] (h : ConjunctionClass255 G) : ConjunctionClass255_long G := by
  obtain ⟨eq4276, eq4293, eq4320, eq4512⟩ := h
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4320, eq4512⟩

theorem CC255_implied_by_long (G : Type*) [Magma G] : ConjunctionClass255_long G -> ConjunctionClass255 G :=
fun ⟨_, h4276, h4293, h4320, h4512⟩ => ⟨h4276, h4293, h4320, h4512⟩

theorem CC255_equiv (G : Type*) [Magma G] : ConjunctionClass255 G <-> ConjunctionClass255_long G :=
Iff.intro (CC255_implies_long G) (CC255_implied_by_long G)

theorem CC256_implies_long (G : Type*) [Magma G] (h : ConjunctionClass256 G) : ConjunctionClass256_long G := by
  obtain ⟨eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC256_implied_by_long (G : Type*) [Magma G] : ConjunctionClass256_long G -> ConjunctionClass256 G :=
fun ⟨_, h4314, h4320, _, _, h4512⟩ => ⟨h4314, h4320, h4512⟩

theorem CC256_equiv (G : Type*) [Magma G] : ConjunctionClass256 G <-> ConjunctionClass256_long G :=
Iff.intro (CC256_implies_long G) (CC256_implied_by_long G)

theorem CC257_implies_long (G : Type*) [Magma G] (h : ConjunctionClass257 G) : ConjunctionClass257_long G := by
  obtain ⟨eq307, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC257_implied_by_long (G : Type*) [Magma G] : ConjunctionClass257_long G -> ConjunctionClass257 G :=
fun ⟨_, h307, _, h4314, h4320, _, _, h4512⟩ => ⟨h307, h4314, h4320, h4512⟩

theorem CC257_equiv (G : Type*) [Magma G] : ConjunctionClass257 G <-> ConjunctionClass257_long G :=
Iff.intro (CC257_implies_long G) (CC257_implied_by_long G)

theorem CC258_implies_long (G : Type*) [Magma G] (h : ConjunctionClass258 G) : ConjunctionClass258_long G := by
  obtain ⟨eq323, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  have eq4362 := Equation323_4321_4512_implies_Equation4362 G eq323 eq4321 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem CC258_implied_by_long (G : Type*) [Magma G] : ConjunctionClass258_long G -> ConjunctionClass258 G :=
fun ⟨_, _, h323, _, _, h4314, h4320, _, _, _, h4512⟩ => ⟨h323, h4314, h4320, h4512⟩

theorem CC258_equiv (G : Type*) [Magma G] : ConjunctionClass258 G <-> ConjunctionClass258_long G :=
Iff.intro (CC258_implies_long G) (CC258_implied_by_long G)

theorem CC259_implies_long (G : Type*) [Magma G] (h : ConjunctionClass259 G) : ConjunctionClass259_long G := by
  obtain ⟨eq4268, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC259_implied_by_long (G : Type*) [Magma G] : ConjunctionClass259_long G -> ConjunctionClass259 G :=
fun ⟨_, h4268, _, _, _, _, h4314, h4320, _, _, h4512⟩ => ⟨h4268, h4314, h4320, h4512⟩

theorem CC259_equiv (G : Type*) [Magma G] : ConjunctionClass259 G <-> ConjunctionClass259_long G :=
Iff.intro (CC259_implies_long G) (CC259_implied_by_long G)

theorem CC260_implies_long (G : Type*) [Magma G] (h : ConjunctionClass260 G) : ConjunctionClass260_long G := by
  obtain ⟨eq4276, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC260_implied_by_long (G : Type*) [Magma G] : ConjunctionClass260_long G -> ConjunctionClass260 G :=
fun ⟨_, h4276, h4314, h4320, _, _, h4512⟩ => ⟨h4276, h4314, h4320, h4512⟩

theorem CC260_equiv (G : Type*) [Magma G] : ConjunctionClass260 G <-> ConjunctionClass260_long G :=
Iff.intro (CC260_implies_long G) (CC260_implied_by_long G)

theorem CC261_implies_long (G : Type*) [Magma G] (h : ConjunctionClass261 G) : ConjunctionClass261_long G := by
  obtain ⟨eq4293, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC261_implied_by_long (G : Type*) [Magma G] : ConjunctionClass261_long G -> ConjunctionClass261 G :=
fun ⟨_, h4293, h4314, h4320, _, _, h4512⟩ => ⟨h4293, h4314, h4320, h4512⟩

theorem CC261_equiv (G : Type*) [Magma G] : ConjunctionClass261 G <-> ConjunctionClass261_long G :=
Iff.intro (CC261_implies_long G) (CC261_implied_by_long G)

theorem CC262_implies_long (G : Type*) [Magma G] (h : ConjunctionClass262 G) : ConjunctionClass262_long G := by
  obtain ⟨eq4276, eq4293, eq4314, eq4320, eq4512⟩ := h
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  have eq1 := Equation4320_4512_implies_Equation1 G eq4320 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4314, eq4320, eq4321, eq4343, eq4512⟩

theorem CC262_implied_by_long (G : Type*) [Magma G] : ConjunctionClass262_long G -> ConjunctionClass262 G :=
fun ⟨_, h4276, h4293, h4314, h4320, _, _, h4512⟩ => ⟨h4276, h4293, h4314, h4320, h4512⟩

theorem CC262_equiv (G : Type*) [Magma G] : ConjunctionClass262 G <-> ConjunctionClass262_long G :=
Iff.intro (CC262_implies_long G) (CC262_implied_by_long G)

theorem CC263_implies_long (G : Type*) [Magma G] (h : ConjunctionClass263 G) : ConjunctionClass263_long G := by
  obtain ⟨eq4321, eq4512⟩ := h
  have eq1 := Equation4321_4512_implies_Equation1 G eq4321 eq4512
  exact ⟨eq1, eq4321, eq4512⟩

theorem CC263_implied_by_long (G : Type*) [Magma G] : ConjunctionClass263_long G -> ConjunctionClass263 G :=
fun ⟨_, h4321, h4512⟩ => ⟨h4321, h4512⟩

theorem CC263_equiv (G : Type*) [Magma G] : ConjunctionClass263 G <-> ConjunctionClass263_long G :=
Iff.intro (CC263_implies_long G) (CC263_implied_by_long G)

theorem CC264_implies_long (G : Type*) [Magma G] (h : ConjunctionClass264 G) : ConjunctionClass264_long G := by
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

theorem CC264_implied_by_long (G : Type*) [Magma G] : ConjunctionClass264_long G -> ConjunctionClass264 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h40, h4321, h4512⟩

theorem CC264_equiv (G : Type*) [Magma G] : ConjunctionClass264 G <-> ConjunctionClass264_long G :=
Iff.intro (CC264_implies_long G) (CC264_implied_by_long G)

theorem CC265_implies_long (G : Type*) [Magma G] (h : ConjunctionClass265 G) : ConjunctionClass265_long G := by
  obtain ⟨eq307, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4321, eq4512⟩

theorem CC265_implied_by_long (G : Type*) [Magma G] : ConjunctionClass265_long G -> ConjunctionClass265 G :=
fun ⟨_, h307, _, h4321, h4512⟩ => ⟨h307, h4321, h4512⟩

theorem CC265_equiv (G : Type*) [Magma G] : ConjunctionClass265 G <-> ConjunctionClass265_long G :=
Iff.intro (CC265_implies_long G) (CC265_implied_by_long G)

theorem CC266_implies_long (G : Type*) [Magma G] (h : ConjunctionClass266 G) : ConjunctionClass266_long G := by
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

theorem CC266_implied_by_long (G : Type*) [Magma G] : ConjunctionClass266_long G -> ConjunctionClass266 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3260, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3260, h4321, h4512⟩

theorem CC266_equiv (G : Type*) [Magma G] : ConjunctionClass266 G <-> ConjunctionClass266_long G :=
Iff.intro (CC266_implies_long G) (CC266_implied_by_long G)

theorem CC267_implies_long (G : Type*) [Magma G] (h : ConjunctionClass267 G) : ConjunctionClass267_long G := by
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

theorem CC267_implied_by_long (G : Type*) [Magma G] : ConjunctionClass267_long G -> ConjunctionClass267 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3265, h4321, h4512⟩

theorem CC267_equiv (G : Type*) [Magma G] : ConjunctionClass267 G <-> ConjunctionClass267_long G :=
Iff.intro (CC267_implies_long G) (CC267_implied_by_long G)

theorem CC268_implies_long (G : Type*) [Magma G] (h : ConjunctionClass268 G) : ConjunctionClass268_long G := by
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

theorem CC268_implied_by_long (G : Type*) [Magma G] : ConjunctionClass268_long G -> ConjunctionClass268 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h3260, _, _, h3265, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3260, h3265, h4321, h4512⟩

theorem CC268_equiv (G : Type*) [Magma G] : ConjunctionClass268 G <-> ConjunctionClass268_long G :=
Iff.intro (CC268_implies_long G) (CC268_implied_by_long G)

theorem CC269_implies_long (G : Type*) [Magma G] (h : ConjunctionClass269 G) : ConjunctionClass269_long G := by
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

theorem CC269_implied_by_long (G : Type*) [Magma G] : ConjunctionClass269_long G -> ConjunctionClass269 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h3267, h4321, h4512⟩

theorem CC269_equiv (G : Type*) [Magma G] : ConjunctionClass269 G <-> ConjunctionClass269_long G :=
Iff.intro (CC269_implies_long G) (CC269_implied_by_long G)

theorem CC270_implies_long (G : Type*) [Magma G] (h : ConjunctionClass270 G) : ConjunctionClass270_long G := by
  obtain ⟨eq4268, eq4321, eq4512⟩ := h
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4321, eq4512⟩

theorem CC270_implied_by_long (G : Type*) [Magma G] : ConjunctionClass270_long G -> ConjunctionClass270 G :=
fun ⟨_, h4268, _, _, _, _, h4321, h4512⟩ => ⟨h4268, h4321, h4512⟩

theorem CC270_equiv (G : Type*) [Magma G] : ConjunctionClass270 G <-> ConjunctionClass270_long G :=
Iff.intro (CC270_implies_long G) (CC270_implied_by_long G)

theorem CC271_implies_long (G : Type*) [Magma G] (h : ConjunctionClass271 G) : ConjunctionClass271_long G := by
  obtain ⟨eq4270, eq4321, eq4512⟩ := h
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4321, eq4343, eq4512⟩

theorem CC271_implied_by_long (G : Type*) [Magma G] : ConjunctionClass271_long G -> ConjunctionClass271 G :=
fun ⟨_, h4270, _, _, _, h4321, _, h4512⟩ => ⟨h4270, h4321, h4512⟩

theorem CC271_equiv (G : Type*) [Magma G] : ConjunctionClass271 G <-> ConjunctionClass271_long G :=
Iff.intro (CC271_implies_long G) (CC271_implied_by_long G)

theorem CC272_implies_long (G : Type*) [Magma G] (h : ConjunctionClass272 G) : ConjunctionClass272_long G := by
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

theorem CC272_implied_by_long (G : Type*) [Magma G] : ConjunctionClass272_long G -> ConjunctionClass272 G :=
fun ⟨_, h4268, h4270, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4512⟩ => ⟨h4268, h4270, h4321, h4512⟩

theorem CC272_equiv (G : Type*) [Magma G] : ConjunctionClass272 G <-> ConjunctionClass272_long G :=
Iff.intro (CC272_implies_long G) (CC272_implied_by_long G)

theorem CC273_implies_long (G : Type*) [Magma G] (h : ConjunctionClass273 G) : ConjunctionClass273_long G := by
  obtain ⟨eq4276, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4321, eq4512⟩

theorem CC273_implied_by_long (G : Type*) [Magma G] : ConjunctionClass273_long G -> ConjunctionClass273 G :=
fun ⟨_, h4276, h4321, h4512⟩ => ⟨h4276, h4321, h4512⟩

theorem CC273_equiv (G : Type*) [Magma G] : ConjunctionClass273 G <-> ConjunctionClass273_long G :=
Iff.intro (CC273_implies_long G) (CC273_implied_by_long G)

theorem CC274_implies_long (G : Type*) [Magma G] (h : ConjunctionClass274 G) : ConjunctionClass274_long G := by
  obtain ⟨eq4284, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4321, eq4512⟩

theorem CC274_implied_by_long (G : Type*) [Magma G] : ConjunctionClass274_long G -> ConjunctionClass274 G :=
fun ⟨_, h4284, h4321, h4512⟩ => ⟨h4284, h4321, h4512⟩

theorem CC274_equiv (G : Type*) [Magma G] : ConjunctionClass274 G <-> ConjunctionClass274_long G :=
Iff.intro (CC274_implies_long G) (CC274_implied_by_long G)

theorem CC275_implies_long (G : Type*) [Magma G] (h : ConjunctionClass275 G) : ConjunctionClass275_long G := by
  obtain ⟨eq307, eq4284, eq4321, eq4512⟩ := h
  have eq4293 := Equation307_4284_4321_4512_implies_Equation4293 G eq307 eq4284 eq4321 eq4512
  have eq4290 := Equation4284_4293_4512_implies_Equation4290 G eq4284 eq4293 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem CC275_implied_by_long (G : Type*) [Magma G] : ConjunctionClass275_long G -> ConjunctionClass275 G :=
fun ⟨_, h307, _, h4284, _, _, h4321, _, h4512⟩ => ⟨h307, h4284, h4321, h4512⟩

theorem CC275_equiv (G : Type*) [Magma G] : ConjunctionClass275 G <-> ConjunctionClass275_long G :=
Iff.intro (CC275_implies_long G) (CC275_implied_by_long G)

theorem CC276_implies_long (G : Type*) [Magma G] (h : ConjunctionClass276 G) : ConjunctionClass276_long G := by
  obtain ⟨eq4276, eq4284, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4321, eq4512⟩

theorem CC276_implied_by_long (G : Type*) [Magma G] : ConjunctionClass276_long G -> ConjunctionClass276 G :=
fun ⟨_, h4276, h4284, h4321, h4512⟩ => ⟨h4276, h4284, h4321, h4512⟩

theorem CC276_equiv (G : Type*) [Magma G] : ConjunctionClass276 G <-> ConjunctionClass276_long G :=
Iff.intro (CC276_implies_long G) (CC276_implied_by_long G)

theorem CC277_implies_long (G : Type*) [Magma G] (h : ConjunctionClass277 G) : ConjunctionClass277_long G := by
  obtain ⟨eq4290, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4290, eq4321, eq4512⟩

theorem CC277_implied_by_long (G : Type*) [Magma G] : ConjunctionClass277_long G -> ConjunctionClass277 G :=
fun ⟨_, h4290, h4321, h4512⟩ => ⟨h4290, h4321, h4512⟩

theorem CC277_equiv (G : Type*) [Magma G] : ConjunctionClass277 G <-> ConjunctionClass277_long G :=
Iff.intro (CC277_implies_long G) (CC277_implied_by_long G)

theorem CC278_implies_long (G : Type*) [Magma G] (h : ConjunctionClass278 G) : ConjunctionClass278_long G := by
  obtain ⟨eq4276, eq4290, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4290, eq4321, eq4512⟩

theorem CC278_implied_by_long (G : Type*) [Magma G] : ConjunctionClass278_long G -> ConjunctionClass278 G :=
fun ⟨_, h4276, h4290, h4321, h4512⟩ => ⟨h4276, h4290, h4321, h4512⟩

theorem CC278_equiv (G : Type*) [Magma G] : ConjunctionClass278 G <-> ConjunctionClass278_long G :=
Iff.intro (CC278_implies_long G) (CC278_implied_by_long G)

theorem CC279_implies_long (G : Type*) [Magma G] (h : ConjunctionClass279 G) : ConjunctionClass279_long G := by
  obtain ⟨eq4284, eq4290, eq4321, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem CC279_implied_by_long (G : Type*) [Magma G] : ConjunctionClass279_long G -> ConjunctionClass279 G :=
fun ⟨_, h4284, h4290, _, h4321, _, h4512⟩ => ⟨h4284, h4290, h4321, h4512⟩

theorem CC279_equiv (G : Type*) [Magma G] : ConjunctionClass279 G <-> ConjunctionClass279_long G :=
Iff.intro (CC279_implies_long G) (CC279_implied_by_long G)

theorem CC280_implies_long (G : Type*) [Magma G] (h : ConjunctionClass280 G) : ConjunctionClass280_long G := by
  obtain ⟨eq4276, eq4284, eq4290, eq4321, eq4512⟩ := h
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4321, eq4343, eq4512⟩

theorem CC280_implied_by_long (G : Type*) [Magma G] : ConjunctionClass280_long G -> ConjunctionClass280 G :=
fun ⟨_, h4276, h4284, h4290, _, h4321, _, h4512⟩ => ⟨h4276, h4284, h4290, h4321, h4512⟩

theorem CC280_equiv (G : Type*) [Magma G] : ConjunctionClass280 G <-> ConjunctionClass280_long G :=
Iff.intro (CC280_implies_long G) (CC280_implied_by_long G)

theorem CC281_implies_long (G : Type*) [Magma G] (h : ConjunctionClass281 G) : ConjunctionClass281_long G := by
  obtain ⟨eq4293, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4321, eq4512⟩

theorem CC281_implied_by_long (G : Type*) [Magma G] : ConjunctionClass281_long G -> ConjunctionClass281 G :=
fun ⟨_, h4293, h4321, h4512⟩ => ⟨h4293, h4321, h4512⟩

theorem CC281_equiv (G : Type*) [Magma G] : ConjunctionClass281 G <-> ConjunctionClass281_long G :=
Iff.intro (CC281_implies_long G) (CC281_implied_by_long G)

theorem CC282_implies_long (G : Type*) [Magma G] (h : ConjunctionClass282 G) : ConjunctionClass282_long G := by
  obtain ⟨eq307, eq4293, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4293, eq4321, eq4512⟩

theorem CC282_implied_by_long (G : Type*) [Magma G] : ConjunctionClass282_long G -> ConjunctionClass282 G :=
fun ⟨_, h307, _, h4293, h4321, h4512⟩ => ⟨h307, h4293, h4321, h4512⟩

theorem CC282_equiv (G : Type*) [Magma G] : ConjunctionClass282 G <-> ConjunctionClass282_long G :=
Iff.intro (CC282_implies_long G) (CC282_implied_by_long G)

theorem CC283_implies_long (G : Type*) [Magma G] (h : ConjunctionClass283 G) : ConjunctionClass283_long G := by
  obtain ⟨eq4270, eq4293, eq4321, eq4512⟩ := h
  have eq4272 := Equation4270_4321_4512_implies_Equation4272 G eq4270 eq4321 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4293, eq4321, eq4343, eq4512⟩

theorem CC283_implied_by_long (G : Type*) [Magma G] : ConjunctionClass283_long G -> ConjunctionClass283 G :=
fun ⟨_, h4270, _, _, _, h4293, h4321, _, h4512⟩ => ⟨h4270, h4293, h4321, h4512⟩

theorem CC283_equiv (G : Type*) [Magma G] : ConjunctionClass283 G <-> ConjunctionClass283_long G :=
Iff.intro (CC283_implies_long G) (CC283_implied_by_long G)

theorem CC284_implies_long (G : Type*) [Magma G] (h : ConjunctionClass284 G) : ConjunctionClass284_long G := by
  obtain ⟨eq4276, eq4293, eq4321, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4321, eq4512⟩

theorem CC284_implied_by_long (G : Type*) [Magma G] : ConjunctionClass284_long G -> ConjunctionClass284 G :=
fun ⟨_, h4276, h4293, h4321, h4512⟩ => ⟨h4276, h4293, h4321, h4512⟩

theorem CC284_equiv (G : Type*) [Magma G] : ConjunctionClass284 G <-> ConjunctionClass284_long G :=
Iff.intro (CC284_implies_long G) (CC284_implied_by_long G)

theorem CC285_implies_long (G : Type*) [Magma G] (h : ConjunctionClass285 G) : ConjunctionClass285_long G := by
  obtain ⟨eq4343, eq4512⟩ := h
  have eq1 := Equation4343_4512_implies_Equation1 G eq4343 eq4512
  exact ⟨eq1, eq4343, eq4512⟩

theorem CC285_implied_by_long (G : Type*) [Magma G] : ConjunctionClass285_long G -> ConjunctionClass285 G :=
fun ⟨_, h4343, h4512⟩ => ⟨h4343, h4512⟩

theorem CC285_equiv (G : Type*) [Magma G] : ConjunctionClass285 G <-> ConjunctionClass285_long G :=
Iff.intro (CC285_implies_long G) (CC285_implied_by_long G)

theorem CC286_implies_long (G : Type*) [Magma G] (h : ConjunctionClass286 G) : ConjunctionClass286_long G := by
  obtain ⟨eq307, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4343, eq4512⟩

theorem CC286_implied_by_long (G : Type*) [Magma G] : ConjunctionClass286_long G -> ConjunctionClass286 G :=
fun ⟨_, h307, _, h4343, h4512⟩ => ⟨h307, h4343, h4512⟩

theorem CC286_equiv (G : Type*) [Magma G] : ConjunctionClass286 G <-> ConjunctionClass286_long G :=
Iff.intro (CC286_implies_long G) (CC286_implied_by_long G)

theorem CC287_implies_long (G : Type*) [Magma G] (h : ConjunctionClass287 G) : ConjunctionClass287_long G := by
  obtain ⟨eq4268, eq4343, eq4512⟩ := h
  have eq4275 := Equation4268_4343_4512_implies_Equation4275 G eq4268 eq4343 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4343, eq4512⟩

theorem CC287_implied_by_long (G : Type*) [Magma G] : ConjunctionClass287_long G -> ConjunctionClass287 G :=
fun ⟨_, h4268, _, _, _, _, h4343, h4512⟩ => ⟨h4268, h4343, h4512⟩

theorem CC287_equiv (G : Type*) [Magma G] : ConjunctionClass287 G <-> ConjunctionClass287_long G :=
Iff.intro (CC287_implies_long G) (CC287_implied_by_long G)

theorem CC288_implies_long (G : Type*) [Magma G] (h : ConjunctionClass288 G) : ConjunctionClass288_long G := by
  obtain ⟨eq4269, eq4343, eq4512⟩ := h
  have eq4273 := Equation4269_4343_4512_implies_Equation4273 G eq4269 eq4343 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4321, eq4343, eq4512⟩

theorem CC288_implied_by_long (G : Type*) [Magma G] : ConjunctionClass288_long G -> ConjunctionClass288 G :=
fun ⟨_, h4269, _, _, _, _, h4343, h4512⟩ => ⟨h4269, h4343, h4512⟩

theorem CC288_equiv (G : Type*) [Magma G] : ConjunctionClass288 G <-> ConjunctionClass288_long G :=
Iff.intro (CC288_implies_long G) (CC288_implied_by_long G)

theorem CC289_implies_long (G : Type*) [Magma G] (h : ConjunctionClass289 G) : ConjunctionClass289_long G := by
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

theorem CC289_implied_by_long (G : Type*) [Magma G] : ConjunctionClass289_long G -> ConjunctionClass289 G :=
fun ⟨_, h4268, h4269, _, _, _, _, _, _, _, _, _, _, _, _, _, h4343, h4512⟩ => ⟨h4268, h4269, h4343, h4512⟩

theorem CC289_equiv (G : Type*) [Magma G] : ConjunctionClass289 G <-> ConjunctionClass289_long G :=
Iff.intro (CC289_implies_long G) (CC289_implied_by_long G)

theorem CC290_implies_long (G : Type*) [Magma G] (h : ConjunctionClass290 G) : ConjunctionClass290_long G := by
  obtain ⟨eq4276, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4343, eq4512⟩

theorem CC290_implied_by_long (G : Type*) [Magma G] : ConjunctionClass290_long G -> ConjunctionClass290 G :=
fun ⟨_, h4276, h4343, h4512⟩ => ⟨h4276, h4343, h4512⟩

theorem CC290_equiv (G : Type*) [Magma G] : ConjunctionClass290 G <-> ConjunctionClass290_long G :=
Iff.intro (CC290_implies_long G) (CC290_implied_by_long G)

theorem CC291_implies_long (G : Type*) [Magma G] (h : ConjunctionClass291 G) : ConjunctionClass291_long G := by
  obtain ⟨eq4283, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4343, eq4512⟩

theorem CC291_implied_by_long (G : Type*) [Magma G] : ConjunctionClass291_long G -> ConjunctionClass291 G :=
fun ⟨_, h4283, h4343, h4512⟩ => ⟨h4283, h4343, h4512⟩

theorem CC291_equiv (G : Type*) [Magma G] : ConjunctionClass291 G <-> ConjunctionClass291_long G :=
Iff.intro (CC291_implies_long G) (CC291_implied_by_long G)

theorem CC292_implies_long (G : Type*) [Magma G] (h : ConjunctionClass292 G) : ConjunctionClass292_long G := by
  obtain ⟨eq4276, eq4283, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4343, eq4512⟩

theorem CC292_implied_by_long (G : Type*) [Magma G] : ConjunctionClass292_long G -> ConjunctionClass292 G :=
fun ⟨_, h4276, h4283, h4343, h4512⟩ => ⟨h4276, h4283, h4343, h4512⟩

theorem CC292_equiv (G : Type*) [Magma G] : ConjunctionClass292 G <-> ConjunctionClass292_long G :=
Iff.intro (CC292_implies_long G) (CC292_implied_by_long G)

theorem CC293_implies_long (G : Type*) [Magma G] (h : ConjunctionClass293 G) : ConjunctionClass293_long G := by
  obtain ⟨eq4291, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4291, eq4343, eq4512⟩

theorem CC293_implied_by_long (G : Type*) [Magma G] : ConjunctionClass293_long G -> ConjunctionClass293 G :=
fun ⟨_, h4291, h4343, h4512⟩ => ⟨h4291, h4343, h4512⟩

theorem CC293_equiv (G : Type*) [Magma G] : ConjunctionClass293 G <-> ConjunctionClass293_long G :=
Iff.intro (CC293_implies_long G) (CC293_implied_by_long G)

theorem CC294_implies_long (G : Type*) [Magma G] (h : ConjunctionClass294 G) : ConjunctionClass294_long G := by
  obtain ⟨eq4276, eq4291, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4291, eq4343, eq4512⟩

theorem CC294_implied_by_long (G : Type*) [Magma G] : ConjunctionClass294_long G -> ConjunctionClass294 G :=
fun ⟨_, h4276, h4291, h4343, h4512⟩ => ⟨h4276, h4291, h4343, h4512⟩

theorem CC294_equiv (G : Type*) [Magma G] : ConjunctionClass294 G <-> ConjunctionClass294_long G :=
Iff.intro (CC294_implies_long G) (CC294_implied_by_long G)

theorem CC295_implies_long (G : Type*) [Magma G] (h : ConjunctionClass295 G) : ConjunctionClass295_long G := by
  obtain ⟨eq4283, eq4291, eq4343, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4343, eq4512⟩

theorem CC295_implied_by_long (G : Type*) [Magma G] : ConjunctionClass295_long G -> ConjunctionClass295 G :=
fun ⟨_, h4283, h4291, _, _, h4343, h4512⟩ => ⟨h4283, h4291, h4343, h4512⟩

theorem CC295_equiv (G : Type*) [Magma G] : ConjunctionClass295 G <-> ConjunctionClass295_long G :=
Iff.intro (CC295_implies_long G) (CC295_implied_by_long G)

theorem CC296_implies_long (G : Type*) [Magma G] (h : ConjunctionClass296 G) : ConjunctionClass296_long G := by
  obtain ⟨eq4276, eq4283, eq4291, eq4343, eq4512⟩ := h
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4343, eq4512⟩

theorem CC296_implied_by_long (G : Type*) [Magma G] : ConjunctionClass296_long G -> ConjunctionClass296 G :=
fun ⟨_, h4276, h4283, h4291, _, _, h4343, h4512⟩ => ⟨h4276, h4283, h4291, h4343, h4512⟩

theorem CC296_equiv (G : Type*) [Magma G] : ConjunctionClass296 G <-> ConjunctionClass296_long G :=
Iff.intro (CC296_implies_long G) (CC296_implied_by_long G)

theorem CC297_implies_long (G : Type*) [Magma G] (h : ConjunctionClass297 G) : ConjunctionClass297_long G := by
  obtain ⟨eq4293, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4343, eq4512⟩

theorem CC297_implied_by_long (G : Type*) [Magma G] : ConjunctionClass297_long G -> ConjunctionClass297 G :=
fun ⟨_, h4293, h4343, h4512⟩ => ⟨h4293, h4343, h4512⟩

theorem CC297_equiv (G : Type*) [Magma G] : ConjunctionClass297 G <-> ConjunctionClass297_long G :=
Iff.intro (CC297_implies_long G) (CC297_implied_by_long G)

theorem CC298_implies_long (G : Type*) [Magma G] (h : ConjunctionClass298 G) : ConjunctionClass298_long G := by
  obtain ⟨eq4269, eq4293, eq4343, eq4512⟩ := h
  have eq4273 := Equation4269_4293_4512_implies_Equation4273 G eq4269 eq4293 eq4512
  have eq1 := Equation4293_4512_implies_Equation1 G eq4293 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4293, eq4321, eq4343, eq4512⟩

theorem CC298_implied_by_long (G : Type*) [Magma G] : ConjunctionClass298_long G -> ConjunctionClass298 G :=
fun ⟨_, h4269, _, _, _, h4293, _, h4343, h4512⟩ => ⟨h4269, h4293, h4343, h4512⟩

theorem CC298_equiv (G : Type*) [Magma G] : ConjunctionClass298 G <-> ConjunctionClass298_long G :=
Iff.intro (CC298_implies_long G) (CC298_implied_by_long G)

theorem CC299_implies_long (G : Type*) [Magma G] (h : ConjunctionClass299 G) : ConjunctionClass299_long G := by
  obtain ⟨eq4276, eq4293, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4343, eq4512⟩

theorem CC299_implied_by_long (G : Type*) [Magma G] : ConjunctionClass299_long G -> ConjunctionClass299 G :=
fun ⟨_, h4276, h4293, h4343, h4512⟩ => ⟨h4276, h4293, h4343, h4512⟩

theorem CC299_equiv (G : Type*) [Magma G] : ConjunctionClass299 G <-> ConjunctionClass299_long G :=
Iff.intro (CC299_implies_long G) (CC299_implied_by_long G)

theorem CC300_implies_long (G : Type*) [Magma G] (h : ConjunctionClass300 G) : ConjunctionClass300_long G := by
  obtain ⟨eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4321, eq4343, eq4512⟩

theorem CC300_implied_by_long (G : Type*) [Magma G] : ConjunctionClass300_long G -> ConjunctionClass300 G :=
fun ⟨_, h4321, h4343, h4512⟩ => ⟨h4321, h4343, h4512⟩

theorem CC300_equiv (G : Type*) [Magma G] : ConjunctionClass300 G <-> ConjunctionClass300_long G :=
Iff.intro (CC300_implies_long G) (CC300_implied_by_long G)

theorem CC301_implies_long (G : Type*) [Magma G] (h : ConjunctionClass301 G) : ConjunctionClass301_long G := by
  obtain ⟨eq307, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4321, eq4343, eq4512⟩

theorem CC301_implied_by_long (G : Type*) [Magma G] : ConjunctionClass301_long G -> ConjunctionClass301 G :=
fun ⟨_, h307, _, h4321, h4343, h4512⟩ => ⟨h307, h4321, h4343, h4512⟩

theorem CC301_equiv (G : Type*) [Magma G] : ConjunctionClass301 G <-> ConjunctionClass301_long G :=
Iff.intro (CC301_implies_long G) (CC301_implied_by_long G)

theorem CC302_implies_long (G : Type*) [Magma G] (h : ConjunctionClass302 G) : ConjunctionClass302_long G := by
  obtain ⟨eq4268, eq4321, eq4343, eq4512⟩ := h
  have eq4275 := Equation4268_4321_4512_implies_Equation4275 G eq4268 eq4321 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4321, eq4343, eq4512⟩

theorem CC302_implied_by_long (G : Type*) [Magma G] : ConjunctionClass302_long G -> ConjunctionClass302 G :=
fun ⟨_, h4268, _, _, _, _, h4321, h4343, h4512⟩ => ⟨h4268, h4321, h4343, h4512⟩

theorem CC302_equiv (G : Type*) [Magma G] : ConjunctionClass302 G <-> ConjunctionClass302_long G :=
Iff.intro (CC302_implies_long G) (CC302_implied_by_long G)

theorem CC303_implies_long (G : Type*) [Magma G] (h : ConjunctionClass303 G) : ConjunctionClass303_long G := by
  obtain ⟨eq4276, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4321, eq4343, eq4512⟩

theorem CC303_implied_by_long (G : Type*) [Magma G] : ConjunctionClass303_long G -> ConjunctionClass303 G :=
fun ⟨_, h4276, h4321, h4343, h4512⟩ => ⟨h4276, h4321, h4343, h4512⟩

theorem CC303_equiv (G : Type*) [Magma G] : ConjunctionClass303 G <-> ConjunctionClass303_long G :=
Iff.intro (CC303_implies_long G) (CC303_implied_by_long G)

theorem CC304_implies_long (G : Type*) [Magma G] (h : ConjunctionClass304 G) : ConjunctionClass304_long G := by
  obtain ⟨eq4293, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4293, eq4321, eq4343, eq4512⟩

theorem CC304_implied_by_long (G : Type*) [Magma G] : ConjunctionClass304_long G -> ConjunctionClass304 G :=
fun ⟨_, h4293, h4321, h4343, h4512⟩ => ⟨h4293, h4321, h4343, h4512⟩

theorem CC304_equiv (G : Type*) [Magma G] : ConjunctionClass304 G <-> ConjunctionClass304_long G :=
Iff.intro (CC304_implies_long G) (CC304_implied_by_long G)

theorem CC305_implies_long (G : Type*) [Magma G] (h : ConjunctionClass305 G) : ConjunctionClass305_long G := by
  obtain ⟨eq4276, eq4293, eq4321, eq4343, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  exact ⟨eq1, eq4276, eq4293, eq4321, eq4343, eq4512⟩

theorem CC305_implied_by_long (G : Type*) [Magma G] : ConjunctionClass305_long G -> ConjunctionClass305 G :=
fun ⟨_, h4276, h4293, h4321, h4343, h4512⟩ => ⟨h4276, h4293, h4321, h4343, h4512⟩

theorem CC305_equiv (G : Type*) [Magma G] : ConjunctionClass305 G <-> ConjunctionClass305_long G :=
Iff.intro (CC305_implies_long G) (CC305_implied_by_long G)

theorem CC306_implies_long (G : Type*) [Magma G] (h : ConjunctionClass306 G) : ConjunctionClass306_long G := by
  obtain ⟨eq4358, eq4512⟩ := h
  have eq1 := Equation4358_4512_implies_Equation1 G eq4358 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4283, eq4358, eq4512⟩

theorem CC306_implied_by_long (G : Type*) [Magma G] : ConjunctionClass306_long G -> ConjunctionClass306 G :=
fun ⟨_, _, h4358, h4512⟩ => ⟨h4358, h4512⟩

theorem CC306_equiv (G : Type*) [Magma G] : ConjunctionClass306 G <-> ConjunctionClass306_long G :=
Iff.intro (CC306_implies_long G) (CC306_implied_by_long G)

theorem CC307_implies_long (G : Type*) [Magma G] (h : ConjunctionClass307 G) : ConjunctionClass307_long G := by
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

theorem CC307_implied_by_long (G : Type*) [Magma G] : ConjunctionClass307_long G -> ConjunctionClass307 G :=
fun ⟨_, h3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h3, h4358, h4512⟩

theorem CC307_equiv (G : Type*) [Magma G] : ConjunctionClass307 G <-> ConjunctionClass307_long G :=
Iff.intro (CC307_implies_long G) (CC307_implied_by_long G)

theorem CC308_implies_long (G : Type*) [Magma G] (h : ConjunctionClass308 G) : ConjunctionClass308_long G := by
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

theorem CC308_implied_by_long (G : Type*) [Magma G] : ConjunctionClass308_long G -> ConjunctionClass308 G :=
fun ⟨_, h8, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h8, h4358, h4512⟩

theorem CC308_equiv (G : Type*) [Magma G] : ConjunctionClass308 G <-> ConjunctionClass308_long G :=
Iff.intro (CC308_implies_long G) (CC308_implied_by_long G)

theorem CC309_implies_long (G : Type*) [Magma G] (h : ConjunctionClass309 G) : ConjunctionClass309_long G := by
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

theorem CC309_implied_by_long (G : Type*) [Magma G] : ConjunctionClass309_long G -> ConjunctionClass309 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h40, h4358, h4512⟩

theorem CC309_equiv (G : Type*) [Magma G] : ConjunctionClass309 G <-> ConjunctionClass309_long G :=
Iff.intro (CC309_implies_long G) (CC309_implied_by_long G)

theorem CC310_implies_long (G : Type*) [Magma G] (h : ConjunctionClass310 G) : ConjunctionClass310_long G := by
  obtain ⟨eq47, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq47, eq4283, eq4358, eq4512⟩

theorem CC310_implied_by_long (G : Type*) [Magma G] : ConjunctionClass310_long G -> ConjunctionClass310 G :=
fun ⟨_, h47, _, h4358, h4512⟩ => ⟨h47, h4358, h4512⟩

theorem CC310_equiv (G : Type*) [Magma G] : ConjunctionClass310 G <-> ConjunctionClass310_long G :=
Iff.intro (CC310_implies_long G) (CC310_implied_by_long G)

theorem CC311_implies_long (G : Type*) [Magma G] (h : ConjunctionClass311 G) : ConjunctionClass311_long G := by
  obtain ⟨eq307, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4358, eq4512⟩

theorem CC311_implied_by_long (G : Type*) [Magma G] : ConjunctionClass311_long G -> ConjunctionClass311 G :=
fun ⟨_, h307, _, _, h4358, h4512⟩ => ⟨h307, h4358, h4512⟩

theorem CC311_equiv (G : Type*) [Magma G] : ConjunctionClass311 G <-> ConjunctionClass311_long G :=
Iff.intro (CC311_implies_long G) (CC311_implied_by_long G)

theorem CC312_implies_long (G : Type*) [Magma G] (h : ConjunctionClass312 G) : ConjunctionClass312_long G := by
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

theorem CC312_implied_by_long (G : Type*) [Magma G] : ConjunctionClass312_long G -> ConjunctionClass312 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h40, h307, h4358, h4512⟩

theorem CC312_equiv (G : Type*) [Magma G] : ConjunctionClass312 G <-> ConjunctionClass312_long G :=
Iff.intro (CC312_implies_long G) (CC312_implied_by_long G)

theorem CC313_implies_long (G : Type*) [Magma G] (h : ConjunctionClass313 G) : ConjunctionClass313_long G := by
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

theorem CC313_implied_by_long (G : Type*) [Magma G] : ConjunctionClass313_long G -> ConjunctionClass313 G :=
fun ⟨_, _, h308, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h308, h4358, h4512⟩

theorem CC313_equiv (G : Type*) [Magma G] : ConjunctionClass313 G <-> ConjunctionClass313_long G :=
Iff.intro (CC313_implies_long G) (CC313_implied_by_long G)

theorem CC314_implies_long (G : Type*) [Magma G] (h : ConjunctionClass314 G) : ConjunctionClass314_long G := by
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

theorem CC314_implied_by_long (G : Type*) [Magma G] : ConjunctionClass314_long G -> ConjunctionClass314 G :=
fun ⟨_, _, h323, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h323, h4358, h4512⟩

theorem CC314_equiv (G : Type*) [Magma G] : ConjunctionClass314 G <-> ConjunctionClass314_long G :=
Iff.intro (CC314_implies_long G) (CC314_implied_by_long G)

theorem CC315_implies_long (G : Type*) [Magma G] (h : ConjunctionClass315 G) : ConjunctionClass315_long G := by
  obtain ⟨eq326, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq307 := Equation326_4512_implies_Equation307 G eq326 eq4512
  have eq3253 := Equation326_4512_implies_Equation3253 G eq326 eq4512
  have eq3319 := Equation326_4512_implies_Equation3319 G eq326 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq307, eq326, eq3253, eq3319, eq4283, eq4358, eq4512⟩

theorem CC315_implied_by_long (G : Type*) [Magma G] : ConjunctionClass315_long G -> ConjunctionClass315 G :=
fun ⟨_, _, h326, _, _, _, h4358, h4512⟩ => ⟨h326, h4358, h4512⟩

theorem CC315_equiv (G : Type*) [Magma G] : ConjunctionClass315 G <-> ConjunctionClass315_long G :=
Iff.intro (CC315_implies_long G) (CC315_implied_by_long G)

theorem CC316_implies_long (G : Type*) [Magma G] (h : ConjunctionClass316 G) : ConjunctionClass316_long G := by
  obtain ⟨eq411, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq411, eq4283, eq4358, eq4512⟩

theorem CC316_implied_by_long (G : Type*) [Magma G] : ConjunctionClass316_long G -> ConjunctionClass316 G :=
fun ⟨_, h411, _, h4358, h4512⟩ => ⟨h411, h4358, h4512⟩

theorem CC316_equiv (G : Type*) [Magma G] : ConjunctionClass316 G <-> ConjunctionClass316_long G :=
Iff.intro (CC316_implies_long G) (CC316_implied_by_long G)

theorem CC317_implies_long (G : Type*) [Magma G] (h : ConjunctionClass317 G) : ConjunctionClass317_long G := by
  obtain ⟨eq3253, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4358, eq4512⟩

theorem CC317_implied_by_long (G : Type*) [Magma G] : ConjunctionClass317_long G -> ConjunctionClass317 G :=
fun ⟨_, h3253, _, h4358, h4512⟩ => ⟨h3253, h4358, h4512⟩

theorem CC317_equiv (G : Type*) [Magma G] : ConjunctionClass317 G <-> ConjunctionClass317_long G :=
Iff.intro (CC317_implies_long G) (CC317_implied_by_long G)

theorem CC318_implies_long (G : Type*) [Magma G] (h : ConjunctionClass318 G) : ConjunctionClass318_long G := by
  obtain ⟨eq3256, eq4358, eq4512⟩ := h
  have eq1 := Equation3256_4512_implies_Equation1 G eq3256 eq4512
  have eq3253 := Equation3256_4512_implies_Equation3253 G eq3256 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3259 := Equation3256_4283_4512_implies_Equation3259 G eq3256 eq4283 eq4512
  have eq3261 := Equation3259_4512_implies_Equation3261 G eq3259 eq4512
  have eq4270 := Equation3259_4512_implies_Equation4270 G eq3259 eq4512
  exact ⟨eq1, eq3253, eq3256, eq3259, eq3261, eq4270, eq4283, eq4358, eq4512⟩

theorem CC318_implied_by_long (G : Type*) [Magma G] : ConjunctionClass318_long G -> ConjunctionClass318 G :=
fun ⟨_, _, h3256, _, _, _, _, h4358, h4512⟩ => ⟨h3256, h4358, h4512⟩

theorem CC318_equiv (G : Type*) [Magma G] : ConjunctionClass318 G <-> ConjunctionClass318_long G :=
Iff.intro (CC318_implies_long G) (CC318_implied_by_long G)

theorem CC319_implies_long (G : Type*) [Magma G] (h : ConjunctionClass319 G) : ConjunctionClass319_long G := by
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

theorem CC319_implied_by_long (G : Type*) [Magma G] : ConjunctionClass319_long G -> ConjunctionClass319 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h3267, h4358, h4512⟩

theorem CC319_equiv (G : Type*) [Magma G] : ConjunctionClass319 G <-> ConjunctionClass319_long G :=
Iff.intro (CC319_implies_long G) (CC319_implied_by_long G)

theorem CC320_implies_long (G : Type*) [Magma G] (h : ConjunctionClass320 G) : ConjunctionClass320_long G := by
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

theorem CC320_implied_by_long (G : Type*) [Magma G] : ConjunctionClass320_long G -> ConjunctionClass320 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h40, h3267, h4358, h4512⟩

theorem CC320_equiv (G : Type*) [Magma G] : ConjunctionClass320 G <-> ConjunctionClass320_long G :=
Iff.intro (CC320_implies_long G) (CC320_implied_by_long G)

theorem CC321_implies_long (G : Type*) [Magma G] (h : ConjunctionClass321 G) : ConjunctionClass321_long G := by
  obtain ⟨eq3306, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3308 := Equation3306_4283_4512_implies_Equation3308 G eq3306 eq4283 eq4512
  have eq3315 := Equation3308_4512_implies_Equation3315 G eq3308 eq4512
  have eq3319 := Equation3308_4512_implies_Equation3319 G eq3308 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3308, eq3315, eq3319, eq4283, eq4358, eq4512⟩

theorem CC321_implied_by_long (G : Type*) [Magma G] : ConjunctionClass321_long G -> ConjunctionClass321 G :=
fun ⟨_, _, h3306, _, _, _, _, h4358, h4512⟩ => ⟨h3306, h4358, h4512⟩

theorem CC321_equiv (G : Type*) [Magma G] : ConjunctionClass321 G <-> ConjunctionClass321_long G :=
Iff.intro (CC321_implies_long G) (CC321_implied_by_long G)

theorem CC322_implies_long (G : Type*) [Magma G] (h : ConjunctionClass322 G) : ConjunctionClass322_long G := by
  obtain ⟨eq3319, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  exact ⟨eq1, eq3253, eq3319, eq4283, eq4358, eq4512⟩

theorem CC322_implied_by_long (G : Type*) [Magma G] : ConjunctionClass322_long G -> ConjunctionClass322 G :=
fun ⟨_, _, h3319, _, h4358, h4512⟩ => ⟨h3319, h4358, h4512⟩

theorem CC322_equiv (G : Type*) [Magma G] : ConjunctionClass322 G <-> ConjunctionClass322_long G :=
Iff.intro (CC322_implies_long G) (CC322_implied_by_long G)

theorem CC323_implies_long (G : Type*) [Magma G] (h : ConjunctionClass323 G) : ConjunctionClass323_long G := by
  obtain ⟨eq4268, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4269 := Equation4268_4283_4512_implies_Equation4269 G eq4268 eq4283 eq4512
  have eq4286 := Equation4268_4269_4512_implies_Equation4286 G eq4268 eq4269 eq4512
  exact ⟨eq1, eq4268, eq4269, eq4283, eq4286, eq4358, eq4512⟩

theorem CC323_implied_by_long (G : Type*) [Magma G] : ConjunctionClass323_long G -> ConjunctionClass323 G :=
fun ⟨_, h4268, _, _, _, h4358, h4512⟩ => ⟨h4268, h4358, h4512⟩

theorem CC323_equiv (G : Type*) [Magma G] : ConjunctionClass323 G <-> ConjunctionClass323_long G :=
Iff.intro (CC323_implies_long G) (CC323_implied_by_long G)

theorem CC324_implies_long (G : Type*) [Magma G] (h : ConjunctionClass324 G) : ConjunctionClass324_long G := by
  obtain ⟨eq4270, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4270, eq4283, eq4358, eq4512⟩

theorem CC324_implied_by_long (G : Type*) [Magma G] : ConjunctionClass324_long G -> ConjunctionClass324 G :=
fun ⟨_, h4270, _, h4358, h4512⟩ => ⟨h4270, h4358, h4512⟩

theorem CC324_equiv (G : Type*) [Magma G] : ConjunctionClass324 G <-> ConjunctionClass324_long G :=
Iff.intro (CC324_implies_long G) (CC324_implied_by_long G)

theorem CC325_implies_long (G : Type*) [Magma G] (h : ConjunctionClass325 G) : ConjunctionClass325_long G := by
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

theorem CC325_implied_by_long (G : Type*) [Magma G] : ConjunctionClass325_long G -> ConjunctionClass325 G :=
fun ⟨_, h4268, _, h4270, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4268, h4270, h4358, h4512⟩

theorem CC325_equiv (G : Type*) [Magma G] : ConjunctionClass325 G <-> ConjunctionClass325_long G :=
Iff.intro (CC325_implies_long G) (CC325_implied_by_long G)

theorem CC326_implies_long (G : Type*) [Magma G] (h : ConjunctionClass326 G) : ConjunctionClass326_long G := by
  obtain ⟨eq4272, eq4358, eq4512⟩ := h
  have eq1 := Equation4272_4512_implies_Equation1 G eq4272 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4270 := Equation4272_4283_4512_implies_Equation4270 G eq4272 eq4283 eq4512
  have eq4280 := Equation4270_4272_4512_implies_Equation4280 G eq4270 eq4272 eq4512
  have eq4276 := Equation4280_4512_implies_Equation4276 G eq4280 eq4512
  have eq4343 := Equation4280_4512_implies_Equation4343 G eq4280 eq4512
  exact ⟨eq1, eq4270, eq4272, eq4276, eq4280, eq4283, eq4343, eq4358, eq4512⟩

theorem CC326_implied_by_long (G : Type*) [Magma G] : ConjunctionClass326_long G -> ConjunctionClass326 G :=
fun ⟨_, _, h4272, _, _, _, _, h4358, h4512⟩ => ⟨h4272, h4358, h4512⟩

theorem CC326_equiv (G : Type*) [Magma G] : ConjunctionClass326 G <-> ConjunctionClass326_long G :=
Iff.intro (CC326_implies_long G) (CC326_implied_by_long G)

theorem CC327_implies_long (G : Type*) [Magma G] (h : ConjunctionClass327 G) : ConjunctionClass327_long G := by
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

theorem CC327_implied_by_long (G : Type*) [Magma G] : ConjunctionClass327_long G -> ConjunctionClass327 G :=
fun ⟨_, h4268, _, _, h4272, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4268, h4272, h4358, h4512⟩

theorem CC327_equiv (G : Type*) [Magma G] : ConjunctionClass327 G <-> ConjunctionClass327_long G :=
Iff.intro (CC327_implies_long G) (CC327_implied_by_long G)

theorem CC328_implies_long (G : Type*) [Magma G] (h : ConjunctionClass328 G) : ConjunctionClass328_long G := by
  obtain ⟨eq4273, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4275 := Equation4273_4283_4512_implies_Equation4275 G eq4273 eq4283 eq4512
  have eq4305 := Equation4273_4275_4512_implies_Equation4305 G eq4273 eq4275 eq4512
  exact ⟨eq1, eq4273, eq4275, eq4283, eq4305, eq4358, eq4512⟩

theorem CC328_implied_by_long (G : Type*) [Magma G] : ConjunctionClass328_long G -> ConjunctionClass328 G :=
fun ⟨_, h4273, _, _, _, h4358, h4512⟩ => ⟨h4273, h4358, h4512⟩

theorem CC328_equiv (G : Type*) [Magma G] : ConjunctionClass328 G <-> ConjunctionClass328_long G :=
Iff.intro (CC328_implies_long G) (CC328_implied_by_long G)

theorem CC329_implies_long (G : Type*) [Magma G] (h : ConjunctionClass329 G) : ConjunctionClass329_long G := by
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

theorem CC329_implied_by_long (G : Type*) [Magma G] : ConjunctionClass329_long G -> ConjunctionClass329 G :=
fun ⟨_, h4268, _, h4273, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4268, h4273, h4358, h4512⟩

theorem CC329_equiv (G : Type*) [Magma G] : ConjunctionClass329 G <-> ConjunctionClass329_long G :=
Iff.intro (CC329_implies_long G) (CC329_implied_by_long G)

theorem CC330_implies_long (G : Type*) [Magma G] (h : ConjunctionClass330 G) : ConjunctionClass330_long G := by
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

theorem CC330_implied_by_long (G : Type*) [Magma G] : ConjunctionClass330_long G -> ConjunctionClass330 G :=
fun ⟨_, h4270, h4273, _, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4270, h4273, h4358, h4512⟩

theorem CC330_equiv (G : Type*) [Magma G] : ConjunctionClass330 G <-> ConjunctionClass330_long G :=
Iff.intro (CC330_implies_long G) (CC330_implied_by_long G)

theorem CC331_implies_long (G : Type*) [Magma G] (h : ConjunctionClass331 G) : ConjunctionClass331_long G := by
  obtain ⟨eq4276, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4358, eq4512⟩

theorem CC331_implied_by_long (G : Type*) [Magma G] : ConjunctionClass331_long G -> ConjunctionClass331 G :=
fun ⟨_, h4276, _, h4358, h4512⟩ => ⟨h4276, h4358, h4512⟩

theorem CC331_equiv (G : Type*) [Magma G] : ConjunctionClass331 G <-> ConjunctionClass331_long G :=
Iff.intro (CC331_implies_long G) (CC331_implied_by_long G)

theorem CC332_implies_long (G : Type*) [Magma G] (h : ConjunctionClass332 G) : ConjunctionClass332_long G := by
  obtain ⟨eq4284, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem CC332_implied_by_long (G : Type*) [Magma G] : ConjunctionClass332_long G -> ConjunctionClass332 G :=
fun ⟨_, _, h4284, _, h4358, h4512⟩ => ⟨h4284, h4358, h4512⟩

theorem CC332_equiv (G : Type*) [Magma G] : ConjunctionClass332 G <-> ConjunctionClass332_long G :=
Iff.intro (CC332_implies_long G) (CC332_implied_by_long G)

theorem CC333_implies_long (G : Type*) [Magma G] (h : ConjunctionClass333 G) : ConjunctionClass333_long G := by
  obtain ⟨eq307, eq4284, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem CC333_implied_by_long (G : Type*) [Magma G] : ConjunctionClass333_long G -> ConjunctionClass333 G :=
fun ⟨_, h307, _, _, h4284, _, h4358, h4512⟩ => ⟨h307, h4284, h4358, h4512⟩

theorem CC333_equiv (G : Type*) [Magma G] : ConjunctionClass333 G <-> ConjunctionClass333_long G :=
Iff.intro (CC333_implies_long G) (CC333_implied_by_long G)

theorem CC334_implies_long (G : Type*) [Magma G] (h : ConjunctionClass334 G) : ConjunctionClass334_long G := by
  obtain ⟨eq4276, eq4284, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4314 := Equation4283_4284_4512_implies_Equation4314 G eq4283 eq4284 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4284, eq4314, eq4358, eq4512⟩

theorem CC334_implied_by_long (G : Type*) [Magma G] : ConjunctionClass334_long G -> ConjunctionClass334 G :=
fun ⟨_, h4276, _, h4284, _, h4358, h4512⟩ => ⟨h4276, h4284, h4358, h4512⟩

theorem CC334_equiv (G : Type*) [Magma G] : ConjunctionClass334 G <-> ConjunctionClass334_long G :=
Iff.intro (CC334_implies_long G) (CC334_implied_by_long G)

theorem CC335_implies_long (G : Type*) [Magma G] (h : ConjunctionClass335 G) : ConjunctionClass335_long G := by
  obtain ⟨eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem CC335_implied_by_long (G : Type*) [Magma G] : ConjunctionClass335_long G -> ConjunctionClass335 G :=
fun ⟨_, _, h4290, _, h4358, h4512⟩ => ⟨h4290, h4358, h4512⟩

theorem CC335_equiv (G : Type*) [Magma G] : ConjunctionClass335 G <-> ConjunctionClass335_long G :=
Iff.intro (CC335_implies_long G) (CC335_implied_by_long G)

theorem CC336_implies_long (G : Type*) [Magma G] (h : ConjunctionClass336 G) : ConjunctionClass336_long G := by
  obtain ⟨eq307, eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem CC336_implied_by_long (G : Type*) [Magma G] : ConjunctionClass336_long G -> ConjunctionClass336 G :=
fun ⟨_, h307, _, _, h4290, _, h4358, h4512⟩ => ⟨h307, h4290, h4358, h4512⟩

theorem CC336_equiv (G : Type*) [Magma G] : ConjunctionClass336 G <-> ConjunctionClass336_long G :=
Iff.intro (CC336_implies_long G) (CC336_implied_by_long G)

theorem CC337_implies_long (G : Type*) [Magma G] (h : ConjunctionClass337 G) : ConjunctionClass337_long G := by
  obtain ⟨eq3253, eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem CC337_implied_by_long (G : Type*) [Magma G] : ConjunctionClass337_long G -> ConjunctionClass337 G :=
fun ⟨_, h3253, _, h4290, _, h4358, h4512⟩ => ⟨h3253, h4290, h4358, h4512⟩

theorem CC337_equiv (G : Type*) [Magma G] : ConjunctionClass337 G <-> ConjunctionClass337_long G :=
Iff.intro (CC337_implies_long G) (CC337_implied_by_long G)

theorem CC338_implies_long (G : Type*) [Magma G] (h : ConjunctionClass338 G) : ConjunctionClass338_long G := by
  obtain ⟨eq4276, eq4290, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4358, eq4512⟩

theorem CC338_implied_by_long (G : Type*) [Magma G] : ConjunctionClass338_long G -> ConjunctionClass338 G :=
fun ⟨_, h4276, _, h4290, _, h4358, h4512⟩ => ⟨h4276, h4290, h4358, h4512⟩

theorem CC338_equiv (G : Type*) [Magma G] : ConjunctionClass338 G <-> ConjunctionClass338_long G :=
Iff.intro (CC338_implies_long G) (CC338_implied_by_long G)

theorem CC339_implies_long (G : Type*) [Magma G] (h : ConjunctionClass339 G) : ConjunctionClass339_long G := by
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

theorem CC339_implied_by_long (G : Type*) [Magma G] : ConjunctionClass339_long G -> ConjunctionClass339 G :=
fun ⟨_, _, h4284, h4290, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4284, h4290, h4358, h4512⟩

theorem CC339_equiv (G : Type*) [Magma G] : ConjunctionClass339 G <-> ConjunctionClass339_long G :=
Iff.intro (CC339_implies_long G) (CC339_implied_by_long G)

theorem CC340_implies_long (G : Type*) [Magma G] (h : ConjunctionClass340 G) : ConjunctionClass340_long G := by
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

theorem CC340_implied_by_long (G : Type*) [Magma G] : ConjunctionClass340_long G -> ConjunctionClass340 G :=
fun ⟨_, h307, _, _, h4284, h4290, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h307, h4284, h4290, h4358, h4512⟩

theorem CC340_equiv (G : Type*) [Magma G] : ConjunctionClass340 G <-> ConjunctionClass340_long G :=
Iff.intro (CC340_implies_long G) (CC340_implied_by_long G)

theorem CC341_implies_long (G : Type*) [Magma G] (h : ConjunctionClass341 G) : ConjunctionClass341_long G := by
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

theorem CC341_implied_by_long (G : Type*) [Magma G] : ConjunctionClass341_long G -> ConjunctionClass341 G :=
fun ⟨_, h4276, _, h4284, h4290, _, _, _, _, _, _, h4358, h4512⟩ => ⟨h4276, h4284, h4290, h4358, h4512⟩

theorem CC341_equiv (G : Type*) [Magma G] : ConjunctionClass341 G <-> ConjunctionClass341_long G :=
Iff.intro (CC341_implies_long G) (CC341_implied_by_long G)

theorem CC342_implies_long (G : Type*) [Magma G] (h : ConjunctionClass342 G) : ConjunctionClass342_long G := by
  obtain ⟨eq4291, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem CC342_implied_by_long (G : Type*) [Magma G] : ConjunctionClass342_long G -> ConjunctionClass342 G :=
fun ⟨_, _, h4291, _, _, h4358, h4512⟩ => ⟨h4291, h4358, h4512⟩

theorem CC342_equiv (G : Type*) [Magma G] : ConjunctionClass342 G <-> ConjunctionClass342_long G :=
Iff.intro (CC342_implies_long G) (CC342_implied_by_long G)

theorem CC343_implies_long (G : Type*) [Magma G] (h : ConjunctionClass343 G) : ConjunctionClass343_long G := by
  obtain ⟨eq307, eq4291, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem CC343_implied_by_long (G : Type*) [Magma G] : ConjunctionClass343_long G -> ConjunctionClass343 G :=
fun ⟨_, h307, _, _, h4291, _, _, h4358, h4512⟩ => ⟨h307, h4291, h4358, h4512⟩

theorem CC343_equiv (G : Type*) [Magma G] : ConjunctionClass343 G <-> ConjunctionClass343_long G :=
Iff.intro (CC343_implies_long G) (CC343_implied_by_long G)

theorem CC344_implies_long (G : Type*) [Magma G] (h : ConjunctionClass344 G) : ConjunctionClass344_long G := by
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

theorem CC344_implied_by_long (G : Type*) [Magma G] : ConjunctionClass344_long G -> ConjunctionClass344 G :=
fun ⟨_, h4270, _, _, _, _, h4291, _, _, _, h4358, h4512⟩ => ⟨h4270, h4291, h4358, h4512⟩

theorem CC344_equiv (G : Type*) [Magma G] : ConjunctionClass344 G <-> ConjunctionClass344_long G :=
Iff.intro (CC344_implies_long G) (CC344_implied_by_long G)

theorem CC345_implies_long (G : Type*) [Magma G] (h : ConjunctionClass345 G) : ConjunctionClass345_long G := by
  obtain ⟨eq4276, eq4291, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4358, eq4512⟩

theorem CC345_implied_by_long (G : Type*) [Magma G] : ConjunctionClass345_long G -> ConjunctionClass345 G :=
fun ⟨_, h4276, _, h4291, _, _, h4358, h4512⟩ => ⟨h4276, h4291, h4358, h4512⟩

theorem CC345_equiv (G : Type*) [Magma G] : ConjunctionClass345 G <-> ConjunctionClass345_long G :=
Iff.intro (CC345_implies_long G) (CC345_implied_by_long G)

theorem CC346_implies_long (G : Type*) [Magma G] (h : ConjunctionClass346 G) : ConjunctionClass346_long G := by
  obtain ⟨eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4283, eq4343, eq4358, eq4512⟩

theorem CC346_implied_by_long (G : Type*) [Magma G] : ConjunctionClass346_long G -> ConjunctionClass346 G :=
fun ⟨_, _, h4343, h4358, h4512⟩ => ⟨h4343, h4358, h4512⟩

theorem CC346_equiv (G : Type*) [Magma G] : ConjunctionClass346 G <-> ConjunctionClass346_long G :=
Iff.intro (CC346_implies_long G) (CC346_implied_by_long G)

theorem CC347_implies_long (G : Type*) [Magma G] (h : ConjunctionClass347 G) : ConjunctionClass347_long G := by
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

theorem CC347_implied_by_long (G : Type*) [Magma G] : ConjunctionClass347_long G -> ConjunctionClass347 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4343, h4358, h4512⟩ => ⟨h4268, h4343, h4358, h4512⟩

theorem CC347_equiv (G : Type*) [Magma G] : ConjunctionClass347 G <-> ConjunctionClass347_long G :=
Iff.intro (CC347_implies_long G) (CC347_implied_by_long G)

theorem CC348_implies_long (G : Type*) [Magma G] (h : ConjunctionClass348 G) : ConjunctionClass348_long G := by
  obtain ⟨eq4276, eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4343, eq4358, eq4512⟩

theorem CC348_implied_by_long (G : Type*) [Magma G] : ConjunctionClass348_long G -> ConjunctionClass348 G :=
fun ⟨_, h4276, _, h4343, h4358, h4512⟩ => ⟨h4276, h4343, h4358, h4512⟩

theorem CC348_equiv (G : Type*) [Magma G] : ConjunctionClass348 G <-> ConjunctionClass348_long G :=
Iff.intro (CC348_implies_long G) (CC348_implied_by_long G)

theorem CC349_implies_long (G : Type*) [Magma G] (h : ConjunctionClass349 G) : ConjunctionClass349_long G := by
  obtain ⟨eq4291, eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4283, eq4291, eq4293, eq4321, eq4343, eq4358, eq4512⟩

theorem CC349_implied_by_long (G : Type*) [Magma G] : ConjunctionClass349_long G -> ConjunctionClass349 G :=
fun ⟨_, _, h4291, _, _, h4343, h4358, h4512⟩ => ⟨h4291, h4343, h4358, h4512⟩

theorem CC349_equiv (G : Type*) [Magma G] : ConjunctionClass349 G <-> ConjunctionClass349_long G :=
Iff.intro (CC349_implies_long G) (CC349_implied_by_long G)

theorem CC350_implies_long (G : Type*) [Magma G] (h : ConjunctionClass350 G) : ConjunctionClass350_long G := by
  obtain ⟨eq4276, eq4291, eq4343, eq4358, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4321 := Equation4283_4291_4512_implies_Equation4321 G eq4283 eq4291 eq4512
  have eq4293 := Equation4283_4291_4512_implies_Equation4293 G eq4283 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4291, eq4293, eq4321, eq4343, eq4358, eq4512⟩

theorem CC350_implied_by_long (G : Type*) [Magma G] : ConjunctionClass350_long G -> ConjunctionClass350 G :=
fun ⟨_, h4276, _, h4291, _, _, h4343, h4358, h4512⟩ => ⟨h4276, h4291, h4343, h4358, h4512⟩

theorem CC350_equiv (G : Type*) [Magma G] : ConjunctionClass350 G <-> ConjunctionClass350_long G :=
Iff.intro (CC350_implies_long G) (CC350_implied_by_long G)

theorem CC351_implies_long (G : Type*) [Magma G] (h : ConjunctionClass351 G) : ConjunctionClass351_long G := by
  obtain ⟨eq4362, eq4512⟩ := h
  have eq1 := Equation4362_4512_implies_Equation1 G eq4362 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4320, eq4362, eq4512⟩

theorem CC351_implied_by_long (G : Type*) [Magma G] : ConjunctionClass351_long G -> ConjunctionClass351 G :=
fun ⟨_, _, h4362, h4512⟩ => ⟨h4362, h4512⟩

theorem CC351_equiv (G : Type*) [Magma G] : ConjunctionClass351 G <-> ConjunctionClass351_long G :=
Iff.intro (CC351_implies_long G) (CC351_implied_by_long G)

theorem CC352_implies_long (G : Type*) [Magma G] (h : ConjunctionClass352 G) : ConjunctionClass352_long G := by
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

theorem CC352_implied_by_long (G : Type*) [Magma G] : ConjunctionClass352_long G -> ConjunctionClass352 G :=
fun ⟨_, h3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h3, h4362, h4512⟩

theorem CC352_equiv (G : Type*) [Magma G] : ConjunctionClass352 G <-> ConjunctionClass352_long G :=
Iff.intro (CC352_implies_long G) (CC352_implied_by_long G)

theorem CC353_implies_long (G : Type*) [Magma G] (h : ConjunctionClass353 G) : ConjunctionClass353_long G := by
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

theorem CC353_implied_by_long (G : Type*) [Magma G] : ConjunctionClass353_long G -> ConjunctionClass353 G :=
fun ⟨_, h8, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h8, h4362, h4512⟩

theorem CC353_equiv (G : Type*) [Magma G] : ConjunctionClass353 G <-> ConjunctionClass353_long G :=
Iff.intro (CC353_implies_long G) (CC353_implied_by_long G)

theorem CC354_implies_long (G : Type*) [Magma G] (h : ConjunctionClass354 G) : ConjunctionClass354_long G := by
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

theorem CC354_implied_by_long (G : Type*) [Magma G] : ConjunctionClass354_long G -> ConjunctionClass354 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h40, h4362, h4512⟩

theorem CC354_equiv (G : Type*) [Magma G] : ConjunctionClass354 G <-> ConjunctionClass354_long G :=
Iff.intro (CC354_implies_long G) (CC354_implied_by_long G)

theorem CC355_implies_long (G : Type*) [Magma G] (h : ConjunctionClass355 G) : ConjunctionClass355_long G := by
  obtain ⟨eq47, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq47, eq4320, eq4362, eq4512⟩

theorem CC355_implied_by_long (G : Type*) [Magma G] : ConjunctionClass355_long G -> ConjunctionClass355 G :=
fun ⟨_, h47, _, h4362, h4512⟩ => ⟨h47, h4362, h4512⟩

theorem CC355_equiv (G : Type*) [Magma G] : ConjunctionClass355 G <-> ConjunctionClass355_long G :=
Iff.intro (CC355_implies_long G) (CC355_implied_by_long G)

theorem CC356_implies_long (G : Type*) [Magma G] (h : ConjunctionClass356 G) : ConjunctionClass356_long G := by
  obtain ⟨eq307, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4320, eq4362, eq4512⟩

theorem CC356_implied_by_long (G : Type*) [Magma G] : ConjunctionClass356_long G -> ConjunctionClass356 G :=
fun ⟨_, h307, _, _, h4362, h4512⟩ => ⟨h307, h4362, h4512⟩

theorem CC356_equiv (G : Type*) [Magma G] : ConjunctionClass356 G <-> ConjunctionClass356_long G :=
Iff.intro (CC356_implies_long G) (CC356_implied_by_long G)

theorem CC357_implies_long (G : Type*) [Magma G] (h : ConjunctionClass357 G) : ConjunctionClass357_long G := by
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

theorem CC357_implied_by_long (G : Type*) [Magma G] : ConjunctionClass357_long G -> ConjunctionClass357 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h40, h307, h4362, h4512⟩

theorem CC357_equiv (G : Type*) [Magma G] : ConjunctionClass357 G <-> ConjunctionClass357_long G :=
Iff.intro (CC357_implies_long G) (CC357_implied_by_long G)

theorem CC358_implies_long (G : Type*) [Magma G] (h : ConjunctionClass358 G) : ConjunctionClass358_long G := by
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

theorem CC358_implied_by_long (G : Type*) [Magma G] : ConjunctionClass358_long G -> ConjunctionClass358 G :=
fun ⟨_, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h309, h4362, h4512⟩

theorem CC358_equiv (G : Type*) [Magma G] : ConjunctionClass358 G <-> ConjunctionClass358_long G :=
Iff.intro (CC358_implies_long G) (CC358_implied_by_long G)

theorem CC359_implies_long (G : Type*) [Magma G] (h : ConjunctionClass359 G) : ConjunctionClass359_long G := by
  obtain ⟨eq323, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq307 := Equation323_4512_implies_Equation307 G eq323 eq4512
  have eq3253 := Equation323_4512_implies_Equation3253 G eq323 eq4512
  have eq3306 := Equation323_4512_implies_Equation3306 G eq323 eq4512
  exact ⟨eq1, eq307, eq323, eq3253, eq3306, eq4320, eq4362, eq4512⟩

theorem CC359_implied_by_long (G : Type*) [Magma G] : ConjunctionClass359_long G -> ConjunctionClass359 G :=
fun ⟨_, _, h323, _, _, _, h4362, h4512⟩ => ⟨h323, h4362, h4512⟩

theorem CC359_equiv (G : Type*) [Magma G] : ConjunctionClass359 G <-> ConjunctionClass359_long G :=
Iff.intro (CC359_implies_long G) (CC359_implied_by_long G)

theorem CC360_implies_long (G : Type*) [Magma G] (h : ConjunctionClass360 G) : ConjunctionClass360_long G := by
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

theorem CC360_implied_by_long (G : Type*) [Magma G] : ConjunctionClass360_long G -> ConjunctionClass360 G :=
fun ⟨_, _, _, h326, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h326, h4362, h4512⟩

theorem CC360_equiv (G : Type*) [Magma G] : ConjunctionClass360 G <-> ConjunctionClass360_long G :=
Iff.intro (CC360_implies_long G) (CC360_implied_by_long G)

theorem CC361_implies_long (G : Type*) [Magma G] (h : ConjunctionClass361 G) : ConjunctionClass361_long G := by
  obtain ⟨eq411, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq411, eq4320, eq4362, eq4512⟩

theorem CC361_implied_by_long (G : Type*) [Magma G] : ConjunctionClass361_long G -> ConjunctionClass361 G :=
fun ⟨_, h411, _, h4362, h4512⟩ => ⟨h411, h4362, h4512⟩

theorem CC361_equiv (G : Type*) [Magma G] : ConjunctionClass361 G <-> ConjunctionClass361_long G :=
Iff.intro (CC361_implies_long G) (CC361_implied_by_long G)

theorem CC362_implies_long (G : Type*) [Magma G] (h : ConjunctionClass362 G) : ConjunctionClass362_long G := by
  obtain ⟨eq3253, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq3253, eq4320, eq4362, eq4512⟩

theorem CC362_implied_by_long (G : Type*) [Magma G] : ConjunctionClass362_long G -> ConjunctionClass362 G :=
fun ⟨_, h3253, _, h4362, h4512⟩ => ⟨h3253, h4362, h4512⟩

theorem CC362_equiv (G : Type*) [Magma G] : ConjunctionClass362 G <-> ConjunctionClass362_long G :=
Iff.intro (CC362_implies_long G) (CC362_implied_by_long G)

theorem CC363_implies_long (G : Type*) [Magma G] (h : ConjunctionClass363 G) : ConjunctionClass363_long G := by
  obtain ⟨eq3261, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation3261_4512_implies_Equation3253 G eq3261 eq4512
  have eq3271 := Equation3261_4320_4512_implies_Equation3271 G eq3261 eq4320 eq4512
  have eq3278 := Equation3271_4512_implies_Equation3278 G eq3271 eq4512
  have eq4275 := Equation3271_4512_implies_Equation4275 G eq3271 eq4512
  exact ⟨eq1, eq3253, eq3261, eq3271, eq3278, eq4275, eq4320, eq4362, eq4512⟩

theorem CC363_implied_by_long (G : Type*) [Magma G] : ConjunctionClass363_long G -> ConjunctionClass363 G :=
fun ⟨_, _, h3261, _, _, _, _, h4362, h4512⟩ => ⟨h3261, h4362, h4512⟩

theorem CC363_equiv (G : Type*) [Magma G] : ConjunctionClass363 G <-> ConjunctionClass363_long G :=
Iff.intro (CC363_implies_long G) (CC363_implied_by_long G)

theorem CC364_implies_long (G : Type*) [Magma G] (h : ConjunctionClass364 G) : ConjunctionClass364_long G := by
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

theorem CC364_implied_by_long (G : Type*) [Magma G] : ConjunctionClass364_long G -> ConjunctionClass364 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h3267, h4362, h4512⟩

theorem CC364_equiv (G : Type*) [Magma G] : ConjunctionClass364 G <-> ConjunctionClass364_long G :=
Iff.intro (CC364_implies_long G) (CC364_implied_by_long G)

theorem CC365_implies_long (G : Type*) [Magma G] (h : ConjunctionClass365 G) : ConjunctionClass365_long G := by
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

theorem CC365_implied_by_long (G : Type*) [Magma G] : ConjunctionClass365_long G -> ConjunctionClass365 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h3300, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h3300, h4362, h4512⟩

theorem CC365_equiv (G : Type*) [Magma G] : ConjunctionClass365 G <-> ConjunctionClass365_long G :=
Iff.intro (CC365_implies_long G) (CC365_implied_by_long G)

theorem CC366_implies_long (G : Type*) [Magma G] (h : ConjunctionClass366 G) : ConjunctionClass366_long G := by
  obtain ⟨eq3306, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation3306_4512_implies_Equation3253 G eq3306 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq3253, eq3306, eq4320, eq4362, eq4512⟩

theorem CC366_implied_by_long (G : Type*) [Magma G] : ConjunctionClass366_long G -> ConjunctionClass366 G :=
fun ⟨_, _, h3306, _, h4362, h4512⟩ => ⟨h3306, h4362, h4512⟩

theorem CC366_equiv (G : Type*) [Magma G] : ConjunctionClass366 G <-> ConjunctionClass366_long G :=
Iff.intro (CC366_implies_long G) (CC366_implied_by_long G)

theorem CC367_implies_long (G : Type*) [Magma G] (h : ConjunctionClass367 G) : ConjunctionClass367_long G := by
  obtain ⟨eq3319, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation3319_4512_implies_Equation3253 G eq3319 eq4512
  have eq3346 := Equation3319_4320_4512_implies_Equation3346 G eq3319 eq4320 eq4512
  have eq3306 := Equation3346_4512_implies_Equation3306 G eq3346 eq4512
  have eq3353 := Equation3346_4512_implies_Equation3353 G eq3346 eq4512
  exact ⟨eq1, eq3253, eq3306, eq3319, eq3346, eq3353, eq4320, eq4362, eq4512⟩

theorem CC367_implied_by_long (G : Type*) [Magma G] : ConjunctionClass367_long G -> ConjunctionClass367 G :=
fun ⟨_, _, _, h3319, _, _, _, h4362, h4512⟩ => ⟨h3319, h4362, h4512⟩

theorem CC367_equiv (G : Type*) [Magma G] : ConjunctionClass367 G <-> ConjunctionClass367_long G :=
Iff.intro (CC367_implies_long G) (CC367_implied_by_long G)

theorem CC368_implies_long (G : Type*) [Magma G] (h : ConjunctionClass368 G) : ConjunctionClass368_long G := by
  obtain ⟨eq4268, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4275 := Equation4268_4320_4512_implies_Equation4275 G eq4268 eq4320 eq4512
  have eq4277 := Equation4268_4275_4512_implies_Equation4277 G eq4268 eq4275 eq4512
  have eq4276 := Equation4277_4512_implies_Equation4276 G eq4277 eq4512
  have eq4293 := Equation4277_4512_implies_Equation4293 G eq4277 eq4512
  exact ⟨eq1, eq4268, eq4275, eq4276, eq4277, eq4293, eq4320, eq4362, eq4512⟩

theorem CC368_implied_by_long (G : Type*) [Magma G] : ConjunctionClass368_long G -> ConjunctionClass368 G :=
fun ⟨_, h4268, _, _, _, _, _, h4362, h4512⟩ => ⟨h4268, h4362, h4512⟩

theorem CC368_equiv (G : Type*) [Magma G] : ConjunctionClass368 G <-> ConjunctionClass368_long G :=
Iff.intro (CC368_implies_long G) (CC368_implied_by_long G)

theorem CC369_implies_long (G : Type*) [Magma G] (h : ConjunctionClass369 G) : ConjunctionClass369_long G := by
  obtain ⟨eq4269, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4272 := Equation4269_4320_4512_implies_Equation4272 G eq4269 eq4320 eq4512
  have eq4327 := Equation4269_4272_4512_implies_Equation4327 G eq4269 eq4272 eq4512
  exact ⟨eq1, eq4269, eq4272, eq4320, eq4327, eq4362, eq4512⟩

theorem CC369_implied_by_long (G : Type*) [Magma G] : ConjunctionClass369_long G -> ConjunctionClass369 G :=
fun ⟨_, h4269, _, _, _, h4362, h4512⟩ => ⟨h4269, h4362, h4512⟩

theorem CC369_equiv (G : Type*) [Magma G] : ConjunctionClass369 G <-> ConjunctionClass369_long G :=
Iff.intro (CC369_implies_long G) (CC369_implied_by_long G)

theorem CC370_implies_long (G : Type*) [Magma G] (h : ConjunctionClass370 G) : ConjunctionClass370_long G := by
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

theorem CC370_implied_by_long (G : Type*) [Magma G] : ConjunctionClass370_long G -> ConjunctionClass370 G :=
fun ⟨_, h4268, h4269, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4268, h4269, h4362, h4512⟩

theorem CC370_equiv (G : Type*) [Magma G] : ConjunctionClass370 G <-> ConjunctionClass370_long G :=
Iff.intro (CC370_implies_long G) (CC370_implied_by_long G)

theorem CC371_implies_long (G : Type*) [Magma G] (h : ConjunctionClass371 G) : ConjunctionClass371_long G := by
  obtain ⟨eq4270, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4273 := Equation4270_4320_4512_implies_Equation4273 G eq4270 eq4320 eq4512
  have eq4325 := Equation4270_4273_4512_implies_Equation4325 G eq4270 eq4273 eq4512
  exact ⟨eq1, eq4270, eq4273, eq4320, eq4325, eq4362, eq4512⟩

theorem CC371_implied_by_long (G : Type*) [Magma G] : ConjunctionClass371_long G -> ConjunctionClass371 G :=
fun ⟨_, h4270, _, _, _, h4362, h4512⟩ => ⟨h4270, h4362, h4512⟩

theorem CC371_equiv (G : Type*) [Magma G] : ConjunctionClass371 G <-> ConjunctionClass371_long G :=
Iff.intro (CC371_implies_long G) (CC371_implied_by_long G)

theorem CC372_implies_long (G : Type*) [Magma G] (h : ConjunctionClass372 G) : ConjunctionClass372_long G := by
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

theorem CC372_implied_by_long (G : Type*) [Magma G] : ConjunctionClass372_long G -> ConjunctionClass372 G :=
fun ⟨_, h4269, h4270, _, _, _, _, _, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4269, h4270, h4362, h4512⟩

theorem CC372_equiv (G : Type*) [Magma G] : ConjunctionClass372 G <-> ConjunctionClass372_long G :=
Iff.intro (CC372_implies_long G) (CC372_implied_by_long G)

theorem CC373_implies_long (G : Type*) [Magma G] (h : ConjunctionClass373 G) : ConjunctionClass373_long G := by
  obtain ⟨eq4275, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4275, eq4320, eq4362, eq4512⟩

theorem CC373_implied_by_long (G : Type*) [Magma G] : ConjunctionClass373_long G -> ConjunctionClass373 G :=
fun ⟨_, h4275, _, h4362, h4512⟩ => ⟨h4275, h4362, h4512⟩

theorem CC373_equiv (G : Type*) [Magma G] : ConjunctionClass373 G <-> ConjunctionClass373_long G :=
Iff.intro (CC373_implies_long G) (CC373_implied_by_long G)

theorem CC374_implies_long (G : Type*) [Magma G] (h : ConjunctionClass374 G) : ConjunctionClass374_long G := by
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

theorem CC374_implied_by_long (G : Type*) [Magma G] : ConjunctionClass374_long G -> ConjunctionClass374 G :=
fun ⟨_, h4269, _, h4275, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4269, h4275, h4362, h4512⟩

theorem CC374_equiv (G : Type*) [Magma G] : ConjunctionClass374 G <-> ConjunctionClass374_long G :=
Iff.intro (CC374_implies_long G) (CC374_implied_by_long G)

theorem CC375_implies_long (G : Type*) [Magma G] (h : ConjunctionClass375 G) : ConjunctionClass375_long G := by
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

theorem CC375_implied_by_long (G : Type*) [Magma G] : ConjunctionClass375_long G -> ConjunctionClass375 G :=
fun ⟨_, h4270, _, h4275, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4270, h4275, h4362, h4512⟩

theorem CC375_equiv (G : Type*) [Magma G] : ConjunctionClass375 G <-> ConjunctionClass375_long G :=
Iff.intro (CC375_implies_long G) (CC375_implied_by_long G)

theorem CC376_implies_long (G : Type*) [Magma G] (h : ConjunctionClass376 G) : ConjunctionClass376_long G := by
  obtain ⟨eq4276, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4276, eq4320, eq4362, eq4512⟩

theorem CC376_implied_by_long (G : Type*) [Magma G] : ConjunctionClass376_long G -> ConjunctionClass376 G :=
fun ⟨_, h4276, _, h4362, h4512⟩ => ⟨h4276, h4362, h4512⟩

theorem CC376_equiv (G : Type*) [Magma G] : ConjunctionClass376 G <-> ConjunctionClass376_long G :=
Iff.intro (CC376_implies_long G) (CC376_implied_by_long G)

theorem CC377_implies_long (G : Type*) [Magma G] (h : ConjunctionClass377 G) : ConjunctionClass377_long G := by
  obtain ⟨eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem CC377_implied_by_long (G : Type*) [Magma G] : ConjunctionClass377_long G -> ConjunctionClass377 G :=
fun ⟨_, h4283, _, _, h4362, h4512⟩ => ⟨h4283, h4362, h4512⟩

theorem CC377_equiv (G : Type*) [Magma G] : ConjunctionClass377 G <-> ConjunctionClass377_long G :=
Iff.intro (CC377_implies_long G) (CC377_implied_by_long G)

theorem CC378_implies_long (G : Type*) [Magma G] (h : ConjunctionClass378 G) : ConjunctionClass378_long G := by
  obtain ⟨eq307, eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem CC378_implied_by_long (G : Type*) [Magma G] : ConjunctionClass378_long G -> ConjunctionClass378 G :=
fun ⟨_, h307, _, h4283, _, _, h4362, h4512⟩ => ⟨h307, h4283, h4362, h4512⟩

theorem CC378_equiv (G : Type*) [Magma G] : ConjunctionClass378 G <-> ConjunctionClass378_long G :=
Iff.intro (CC378_implies_long G) (CC378_implied_by_long G)

theorem CC379_implies_long (G : Type*) [Magma G] (h : ConjunctionClass379 G) : ConjunctionClass379_long G := by
  obtain ⟨eq3253, eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem CC379_implied_by_long (G : Type*) [Magma G] : ConjunctionClass379_long G -> ConjunctionClass379 G :=
fun ⟨_, h3253, h4283, _, _, h4362, h4512⟩ => ⟨h3253, h4283, h4362, h4512⟩

theorem CC379_equiv (G : Type*) [Magma G] : ConjunctionClass379 G <-> ConjunctionClass379_long G :=
Iff.intro (CC379_implies_long G) (CC379_implied_by_long G)

theorem CC380_implies_long (G : Type*) [Magma G] (h : ConjunctionClass380 G) : ConjunctionClass380_long G := by
  obtain ⟨eq4276, eq4283, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4362, eq4512⟩

theorem CC380_implied_by_long (G : Type*) [Magma G] : ConjunctionClass380_long G -> ConjunctionClass380 G :=
fun ⟨_, h4276, h4283, _, _, h4362, h4512⟩ => ⟨h4276, h4283, h4362, h4512⟩

theorem CC380_equiv (G : Type*) [Magma G] : ConjunctionClass380 G <-> ConjunctionClass380_long G :=
Iff.intro (CC380_implies_long G) (CC380_implied_by_long G)

theorem CC381_implies_long (G : Type*) [Magma G] (h : ConjunctionClass381 G) : ConjunctionClass381_long G := by
  obtain ⟨eq4284, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  exact ⟨eq1, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem CC381_implied_by_long (G : Type*) [Magma G] : ConjunctionClass381_long G -> ConjunctionClass381 G :=
fun ⟨_, h4284, _, _, h4362, h4512⟩ => ⟨h4284, h4362, h4512⟩

theorem CC381_equiv (G : Type*) [Magma G] : ConjunctionClass381 G <-> ConjunctionClass381_long G :=
Iff.intro (CC381_implies_long G) (CC381_implied_by_long G)

theorem CC382_implies_long (G : Type*) [Magma G] (h : ConjunctionClass382 G) : ConjunctionClass382_long G := by
  obtain ⟨eq307, eq4284, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem CC382_implied_by_long (G : Type*) [Magma G] : ConjunctionClass382_long G -> ConjunctionClass382 G :=
fun ⟨_, h307, _, h4284, _, _, h4362, h4512⟩ => ⟨h307, h4284, h4362, h4512⟩

theorem CC382_equiv (G : Type*) [Magma G] : ConjunctionClass382 G <-> ConjunctionClass382_long G :=
Iff.intro (CC382_implies_long G) (CC382_implied_by_long G)

theorem CC383_implies_long (G : Type*) [Magma G] (h : ConjunctionClass383 G) : ConjunctionClass383_long G := by
  obtain ⟨eq4276, eq4284, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4291 := Equation4284_4320_4512_implies_Equation4291 G eq4284 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4284, eq4291, eq4320, eq4362, eq4512⟩

theorem CC383_implied_by_long (G : Type*) [Magma G] : ConjunctionClass383_long G -> ConjunctionClass383 G :=
fun ⟨_, h4276, h4284, _, _, h4362, h4512⟩ => ⟨h4276, h4284, h4362, h4512⟩

theorem CC383_equiv (G : Type*) [Magma G] : ConjunctionClass383 G <-> ConjunctionClass383_long G :=
Iff.intro (CC383_implies_long G) (CC383_implied_by_long G)

theorem CC384_implies_long (G : Type*) [Magma G] (h : ConjunctionClass384 G) : ConjunctionClass384_long G := by
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

theorem CC384_implied_by_long (G : Type*) [Magma G] : ConjunctionClass384_long G -> ConjunctionClass384 G :=
fun ⟨_, h4283, h4284, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4283, h4284, h4362, h4512⟩

theorem CC384_equiv (G : Type*) [Magma G] : ConjunctionClass384 G <-> ConjunctionClass384_long G :=
Iff.intro (CC384_implies_long G) (CC384_implied_by_long G)

theorem CC385_implies_long (G : Type*) [Magma G] (h : ConjunctionClass385 G) : ConjunctionClass385_long G := by
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

theorem CC385_implied_by_long (G : Type*) [Magma G] : ConjunctionClass385_long G -> ConjunctionClass385 G :=
fun ⟨_, h307, _, h4283, h4284, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h307, h4283, h4284, h4362, h4512⟩

theorem CC385_equiv (G : Type*) [Magma G] : ConjunctionClass385 G <-> ConjunctionClass385_long G :=
Iff.intro (CC385_implies_long G) (CC385_implied_by_long G)

theorem CC386_implies_long (G : Type*) [Magma G] (h : ConjunctionClass386 G) : ConjunctionClass386_long G := by
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

theorem CC386_implied_by_long (G : Type*) [Magma G] : ConjunctionClass386_long G -> ConjunctionClass386 G :=
fun ⟨_, h4276, h4283, h4284, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4276, h4283, h4284, h4362, h4512⟩

theorem CC386_equiv (G : Type*) [Magma G] : ConjunctionClass386 G <-> ConjunctionClass386_long G :=
Iff.intro (CC386_implies_long G) (CC386_implied_by_long G)

theorem CC387_implies_long (G : Type*) [Magma G] (h : ConjunctionClass387 G) : ConjunctionClass387_long G := by
  obtain ⟨eq4293, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4293, eq4320, eq4362, eq4512⟩

theorem CC387_implied_by_long (G : Type*) [Magma G] : ConjunctionClass387_long G -> ConjunctionClass387 G :=
fun ⟨_, h4293, _, h4362, h4512⟩ => ⟨h4293, h4362, h4512⟩

theorem CC387_equiv (G : Type*) [Magma G] : ConjunctionClass387 G <-> ConjunctionClass387_long G :=
Iff.intro (CC387_implies_long G) (CC387_implied_by_long G)

theorem CC388_implies_long (G : Type*) [Magma G] (h : ConjunctionClass388 G) : ConjunctionClass388_long G := by
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

theorem CC388_implied_by_long (G : Type*) [Magma G] : ConjunctionClass388_long G -> ConjunctionClass388 G :=
fun ⟨_, h4269, _, _, _, _, _, _, h4293, _, _, _, _, _, _, _, _, h4362, h4512⟩ => ⟨h4269, h4293, h4362, h4512⟩

theorem CC388_equiv (G : Type*) [Magma G] : ConjunctionClass388 G <-> ConjunctionClass388_long G :=
Iff.intro (CC388_implies_long G) (CC388_implied_by_long G)

theorem CC389_implies_long (G : Type*) [Magma G] (h : ConjunctionClass389 G) : ConjunctionClass389_long G := by
  obtain ⟨eq4276, eq4293, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4320, eq4362, eq4512⟩

theorem CC389_implied_by_long (G : Type*) [Magma G] : ConjunctionClass389_long G -> ConjunctionClass389 G :=
fun ⟨_, h4276, h4293, _, h4362, h4512⟩ => ⟨h4276, h4293, h4362, h4512⟩

theorem CC389_equiv (G : Type*) [Magma G] : ConjunctionClass389 G <-> ConjunctionClass389_long G :=
Iff.intro (CC389_implies_long G) (CC389_implied_by_long G)

theorem CC390_implies_long (G : Type*) [Magma G] (h : ConjunctionClass390 G) : ConjunctionClass390_long G := by
  obtain ⟨eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem CC390_implied_by_long (G : Type*) [Magma G] : ConjunctionClass390_long G -> ConjunctionClass390 G :=
fun ⟨_, h4314, _, _, _, h4362, h4512⟩ => ⟨h4314, h4362, h4512⟩

theorem CC390_equiv (G : Type*) [Magma G] : ConjunctionClass390 G <-> ConjunctionClass390_long G :=
Iff.intro (CC390_implies_long G) (CC390_implied_by_long G)

theorem CC391_implies_long (G : Type*) [Magma G] (h : ConjunctionClass391 G) : ConjunctionClass391_long G := by
  obtain ⟨eq307, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem CC391_implied_by_long (G : Type*) [Magma G] : ConjunctionClass391_long G -> ConjunctionClass391 G :=
fun ⟨_, h307, _, h4314, _, _, _, h4362, h4512⟩ => ⟨h307, h4314, h4362, h4512⟩

theorem CC391_equiv (G : Type*) [Magma G] : ConjunctionClass391 G <-> ConjunctionClass391_long G :=
Iff.intro (CC391_implies_long G) (CC391_implied_by_long G)

theorem CC392_implies_long (G : Type*) [Magma G] (h : ConjunctionClass392 G) : ConjunctionClass392_long G := by
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

theorem CC392_implied_by_long (G : Type*) [Magma G] : ConjunctionClass392_long G -> ConjunctionClass392 G :=
fun ⟨_, h4268, _, _, _, _, h4314, _, _, _, h4362, h4512⟩ => ⟨h4268, h4314, h4362, h4512⟩

theorem CC392_equiv (G : Type*) [Magma G] : ConjunctionClass392 G <-> ConjunctionClass392_long G :=
Iff.intro (CC392_implies_long G) (CC392_implied_by_long G)

theorem CC393_implies_long (G : Type*) [Magma G] (h : ConjunctionClass393 G) : ConjunctionClass393_long G := by
  obtain ⟨eq4276, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem CC393_implied_by_long (G : Type*) [Magma G] : ConjunctionClass393_long G -> ConjunctionClass393 G :=
fun ⟨_, h4276, h4314, _, _, _, h4362, h4512⟩ => ⟨h4276, h4314, h4362, h4512⟩

theorem CC393_equiv (G : Type*) [Magma G] : ConjunctionClass393 G <-> ConjunctionClass393_long G :=
Iff.intro (CC393_implies_long G) (CC393_implied_by_long G)

theorem CC394_implies_long (G : Type*) [Magma G] (h : ConjunctionClass394 G) : ConjunctionClass394_long G := by
  obtain ⟨eq4293, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem CC394_implied_by_long (G : Type*) [Magma G] : ConjunctionClass394_long G -> ConjunctionClass394 G :=
fun ⟨_, h4293, h4314, _, _, _, h4362, h4512⟩ => ⟨h4293, h4314, h4362, h4512⟩

theorem CC394_equiv (G : Type*) [Magma G] : ConjunctionClass394 G <-> ConjunctionClass394_long G :=
Iff.intro (CC394_implies_long G) (CC394_implied_by_long G)

theorem CC395_implies_long (G : Type*) [Magma G] (h : ConjunctionClass395 G) : ConjunctionClass395_long G := by
  obtain ⟨eq4276, eq4293, eq4314, eq4362, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4321 := Equation4314_4320_4512_implies_Equation4321 G eq4314 eq4320 eq4512
  have eq4343 := Equation4314_4320_4512_implies_Equation4343 G eq4314 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4293, eq4314, eq4320, eq4321, eq4343, eq4362, eq4512⟩

theorem CC395_implied_by_long (G : Type*) [Magma G] : ConjunctionClass395_long G -> ConjunctionClass395 G :=
fun ⟨_, h4276, h4293, h4314, _, _, _, h4362, h4512⟩ => ⟨h4276, h4293, h4314, h4362, h4512⟩

theorem CC395_equiv (G : Type*) [Magma G] : ConjunctionClass395 G <-> ConjunctionClass395_long G :=
Iff.intro (CC395_implies_long G) (CC395_implied_by_long G)

theorem CC396_implies_long (G : Type*) [Magma G] (h : ConjunctionClass396 G) : ConjunctionClass396_long G := by
  obtain ⟨eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem CC396_implied_by_long (G : Type*) [Magma G] : ConjunctionClass396_long G -> ConjunctionClass396 G :=
fun ⟨_, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4358, h4362, h4512⟩

theorem CC396_equiv (G : Type*) [Magma G] : ConjunctionClass396 G <-> ConjunctionClass396_long G :=
Iff.intro (CC396_implies_long G) (CC396_implied_by_long G)

theorem CC397_implies_long (G : Type*) [Magma G] (h : ConjunctionClass397 G) : ConjunctionClass397_long G := by
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

theorem CC397_implied_by_long (G : Type*) [Magma G] : ConjunctionClass397_long G -> ConjunctionClass397 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h40, h4358, h4362, h4512⟩

theorem CC397_equiv (G : Type*) [Magma G] : ConjunctionClass397 G <-> ConjunctionClass397_long G :=
Iff.intro (CC397_implies_long G) (CC397_implied_by_long G)

theorem CC398_implies_long (G : Type*) [Magma G] (h : ConjunctionClass398 G) : ConjunctionClass398_long G := by
  obtain ⟨eq307, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem CC398_implied_by_long (G : Type*) [Magma G] : ConjunctionClass398_long G -> ConjunctionClass398 G :=
fun ⟨_, h307, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h307, h4358, h4362, h4512⟩

theorem CC398_equiv (G : Type*) [Magma G] : ConjunctionClass398 G <-> ConjunctionClass398_long G :=
Iff.intro (CC398_implies_long G) (CC398_implied_by_long G)

theorem CC399_implies_long (G : Type*) [Magma G] (h : ConjunctionClass399 G) : ConjunctionClass399_long G := by
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

theorem CC399_implied_by_long (G : Type*) [Magma G] : ConjunctionClass399_long G -> ConjunctionClass399 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h40, h307, h4358, h4362, h4512⟩

theorem CC399_equiv (G : Type*) [Magma G] : ConjunctionClass399 G <-> ConjunctionClass399_long G :=
Iff.intro (CC399_implies_long G) (CC399_implied_by_long G)

theorem CC400_implies_long (G : Type*) [Magma G] (h : ConjunctionClass400 G) : ConjunctionClass400_long G := by
  obtain ⟨eq3253, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem CC400_implied_by_long (G : Type*) [Magma G] : ConjunctionClass400_long G -> ConjunctionClass400 G :=
fun ⟨_, h3253, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h3253, h4358, h4362, h4512⟩

theorem CC400_equiv (G : Type*) [Magma G] : ConjunctionClass400 G <-> ConjunctionClass400_long G :=
Iff.intro (CC400_implies_long G) (CC400_implied_by_long G)

theorem CC401_implies_long (G : Type*) [Magma G] (h : ConjunctionClass401 G) : ConjunctionClass401_long G := by
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

theorem CC401_implied_by_long (G : Type*) [Magma G] : ConjunctionClass401_long G -> ConjunctionClass401 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h3267, h4358, h4362, h4512⟩

theorem CC401_equiv (G : Type*) [Magma G] : ConjunctionClass401 G <-> ConjunctionClass401_long G :=
Iff.intro (CC401_implies_long G) (CC401_implied_by_long G)

theorem CC402_implies_long (G : Type*) [Magma G] (h : ConjunctionClass402 G) : ConjunctionClass402_long G := by
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

theorem CC402_implied_by_long (G : Type*) [Magma G] : ConjunctionClass402_long G -> ConjunctionClass402 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4268, h4358, h4362, h4512⟩

theorem CC402_equiv (G : Type*) [Magma G] : ConjunctionClass402 G <-> ConjunctionClass402_long G :=
Iff.intro (CC402_implies_long G) (CC402_implied_by_long G)

theorem CC403_implies_long (G : Type*) [Magma G] (h : ConjunctionClass403 G) : ConjunctionClass403_long G := by
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

theorem CC403_implied_by_long (G : Type*) [Magma G] : ConjunctionClass403_long G -> ConjunctionClass403 G :=
fun ⟨_, h4270, _, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4270, h4358, h4362, h4512⟩

theorem CC403_equiv (G : Type*) [Magma G] : ConjunctionClass403 G <-> ConjunctionClass403_long G :=
Iff.intro (CC403_implies_long G) (CC403_implied_by_long G)

theorem CC404_implies_long (G : Type*) [Magma G] (h : ConjunctionClass404 G) : ConjunctionClass404_long G := by
  obtain ⟨eq4276, eq4358, eq4362, eq4512⟩ := h
  have eq4369 := Equation4358_4362_4512_implies_Equation4369 G eq4358 eq4362 eq4512
  have eq4364 := Equation4358_4362_4512_implies_Equation4364 G eq4358 eq4362 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4320 := Equation4362_4512_implies_Equation4320 G eq4362 eq4512
  have eq4283 := Equation4358_4512_implies_Equation4283 G eq4358 eq4512
  have eq4290 := Equation4283_4320_4512_implies_Equation4290 G eq4283 eq4320 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4358, eq4362, eq4364, eq4369, eq4512⟩

theorem CC404_implied_by_long (G : Type*) [Magma G] : ConjunctionClass404_long G -> ConjunctionClass404 G :=
fun ⟨_, h4276, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4276, h4358, h4362, h4512⟩

theorem CC404_equiv (G : Type*) [Magma G] : ConjunctionClass404 G <-> ConjunctionClass404_long G :=
Iff.intro (CC404_implies_long G) (CC404_implied_by_long G)

theorem CC405_implies_long (G : Type*) [Magma G] (h : ConjunctionClass405 G) : ConjunctionClass405_long G := by
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

theorem CC405_implied_by_long (G : Type*) [Magma G] : ConjunctionClass405_long G -> ConjunctionClass405 G :=
fun ⟨_, _, h4284, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4284, h4358, h4362, h4512⟩

theorem CC405_equiv (G : Type*) [Magma G] : ConjunctionClass405 G <-> ConjunctionClass405_long G :=
Iff.intro (CC405_implies_long G) (CC405_implied_by_long G)

theorem CC406_implies_long (G : Type*) [Magma G] (h : ConjunctionClass406 G) : ConjunctionClass406_long G := by
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

theorem CC406_implied_by_long (G : Type*) [Magma G] : ConjunctionClass406_long G -> ConjunctionClass406 G :=
fun ⟨_, h307, _, _, h4284, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h307, h4284, h4358, h4362, h4512⟩

theorem CC406_equiv (G : Type*) [Magma G] : ConjunctionClass406 G <-> ConjunctionClass406_long G :=
Iff.intro (CC406_implies_long G) (CC406_implied_by_long G)

theorem CC407_implies_long (G : Type*) [Magma G] (h : ConjunctionClass407 G) : ConjunctionClass407_long G := by
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

theorem CC407_implied_by_long (G : Type*) [Magma G] : ConjunctionClass407_long G -> ConjunctionClass407 G :=
fun ⟨_, h4276, _, h4284, _, _, _, _, _, _, _, h4358, h4362, _, _, h4512⟩ => ⟨h4276, h4284, h4358, h4362, h4512⟩

theorem CC407_equiv (G : Type*) [Magma G] : ConjunctionClass407 G <-> ConjunctionClass407_long G :=
Iff.intro (CC407_implies_long G) (CC407_implied_by_long G)

theorem CC408_implies_long (G : Type*) [Magma G] (h : ConjunctionClass408 G) : ConjunctionClass408_long G := by
  obtain ⟨eq4364, eq4512⟩ := h
  have eq1 := Equation4364_4512_implies_Equation1 G eq4364 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem CC408_implied_by_long (G : Type*) [Magma G] : ConjunctionClass408_long G -> ConjunctionClass408 G :=
fun ⟨_, _, _, _, h4364, h4512⟩ => ⟨h4364, h4512⟩

theorem CC408_equiv (G : Type*) [Magma G] : ConjunctionClass408 G <-> ConjunctionClass408_long G :=
Iff.intro (CC408_implies_long G) (CC408_implied_by_long G)

theorem CC409_implies_long (G : Type*) [Magma G] (h : ConjunctionClass409 G) : ConjunctionClass409_long G := by
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

theorem CC409_implied_by_long (G : Type*) [Magma G] : ConjunctionClass409_long G -> ConjunctionClass409 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h40, h4364, h4512⟩

theorem CC409_equiv (G : Type*) [Magma G] : ConjunctionClass409 G <-> ConjunctionClass409_long G :=
Iff.intro (CC409_implies_long G) (CC409_implied_by_long G)

theorem CC410_implies_long (G : Type*) [Magma G] (h : ConjunctionClass410 G) : ConjunctionClass410_long G := by
  obtain ⟨eq307, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem CC410_implied_by_long (G : Type*) [Magma G] : ConjunctionClass410_long G -> ConjunctionClass410 G :=
fun ⟨_, h307, _, _, _, _, h4364, h4512⟩ => ⟨h307, h4364, h4512⟩

theorem CC410_equiv (G : Type*) [Magma G] : ConjunctionClass410 G <-> ConjunctionClass410_long G :=
Iff.intro (CC410_implies_long G) (CC410_implied_by_long G)

theorem CC411_implies_long (G : Type*) [Magma G] (h : ConjunctionClass411 G) : ConjunctionClass411_long G := by
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

theorem CC411_implied_by_long (G : Type*) [Magma G] : ConjunctionClass411_long G -> ConjunctionClass411 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h40, h307, h4364, h4512⟩

theorem CC411_equiv (G : Type*) [Magma G] : ConjunctionClass411 G <-> ConjunctionClass411_long G :=
Iff.intro (CC411_implies_long G) (CC411_implied_by_long G)

theorem CC412_implies_long (G : Type*) [Magma G] (h : ConjunctionClass412 G) : ConjunctionClass412_long G := by
  obtain ⟨eq3253, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem CC412_implied_by_long (G : Type*) [Magma G] : ConjunctionClass412_long G -> ConjunctionClass412 G :=
fun ⟨_, h3253, _, _, _, h4364, h4512⟩ => ⟨h3253, h4364, h4512⟩

theorem CC412_equiv (G : Type*) [Magma G] : ConjunctionClass412 G <-> ConjunctionClass412_long G :=
Iff.intro (CC412_implies_long G) (CC412_implied_by_long G)

theorem CC413_implies_long (G : Type*) [Magma G] (h : ConjunctionClass413 G) : ConjunctionClass413_long G := by
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

theorem CC413_implied_by_long (G : Type*) [Magma G] : ConjunctionClass413_long G -> ConjunctionClass413 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h3267, h4364, h4512⟩

theorem CC413_equiv (G : Type*) [Magma G] : ConjunctionClass413 G <-> ConjunctionClass413_long G :=
Iff.intro (CC413_implies_long G) (CC413_implied_by_long G)

theorem CC414_implies_long (G : Type*) [Magma G] (h : ConjunctionClass414 G) : ConjunctionClass414_long G := by
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

theorem CC414_implied_by_long (G : Type*) [Magma G] : ConjunctionClass414_long G -> ConjunctionClass414 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4268, h4364, h4512⟩

theorem CC414_equiv (G : Type*) [Magma G] : ConjunctionClass414 G <-> ConjunctionClass414_long G :=
Iff.intro (CC414_implies_long G) (CC414_implied_by_long G)

theorem CC415_implies_long (G : Type*) [Magma G] (h : ConjunctionClass415 G) : ConjunctionClass415_long G := by
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

theorem CC415_implied_by_long (G : Type*) [Magma G] : ConjunctionClass415_long G -> ConjunctionClass415 G :=
fun ⟨_, h4270, _, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4270, h4364, h4512⟩

theorem CC415_equiv (G : Type*) [Magma G] : ConjunctionClass415 G <-> ConjunctionClass415_long G :=
Iff.intro (CC415_implies_long G) (CC415_implied_by_long G)

theorem CC416_implies_long (G : Type*) [Magma G] (h : ConjunctionClass416 G) : ConjunctionClass416_long G := by
  obtain ⟨eq4276, eq4364, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4283 := Equation4364_4512_implies_Equation4283 G eq4364 eq4512
  have eq4290 := Equation4364_4512_implies_Equation4290 G eq4364 eq4512
  have eq4320 := Equation4364_4512_implies_Equation4320 G eq4364 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4364, eq4512⟩

theorem CC416_implied_by_long (G : Type*) [Magma G] : ConjunctionClass416_long G -> ConjunctionClass416 G :=
fun ⟨_, h4276, _, _, _, h4364, h4512⟩ => ⟨h4276, h4364, h4512⟩

theorem CC416_equiv (G : Type*) [Magma G] : ConjunctionClass416 G <-> ConjunctionClass416_long G :=
Iff.intro (CC416_implies_long G) (CC416_implied_by_long G)

theorem CC417_implies_long (G : Type*) [Magma G] (h : ConjunctionClass417 G) : ConjunctionClass417_long G := by
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

theorem CC417_implied_by_long (G : Type*) [Magma G] : ConjunctionClass417_long G -> ConjunctionClass417 G :=
fun ⟨_, _, h4284, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4284, h4364, h4512⟩

theorem CC417_equiv (G : Type*) [Magma G] : ConjunctionClass417 G <-> ConjunctionClass417_long G :=
Iff.intro (CC417_implies_long G) (CC417_implied_by_long G)

theorem CC418_implies_long (G : Type*) [Magma G] (h : ConjunctionClass418 G) : ConjunctionClass418_long G := by
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

theorem CC418_implied_by_long (G : Type*) [Magma G] : ConjunctionClass418_long G -> ConjunctionClass418 G :=
fun ⟨_, h307, _, _, h4284, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h307, h4284, h4364, h4512⟩

theorem CC418_equiv (G : Type*) [Magma G] : ConjunctionClass418 G <-> ConjunctionClass418_long G :=
Iff.intro (CC418_implies_long G) (CC418_implied_by_long G)

theorem CC419_implies_long (G : Type*) [Magma G] (h : ConjunctionClass419 G) : ConjunctionClass419_long G := by
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

theorem CC419_implied_by_long (G : Type*) [Magma G] : ConjunctionClass419_long G -> ConjunctionClass419 G :=
fun ⟨_, h4276, _, h4284, _, _, _, _, _, _, _, h4364, h4512⟩ => ⟨h4276, h4284, h4364, h4512⟩

theorem CC419_equiv (G : Type*) [Magma G] : ConjunctionClass419 G <-> ConjunctionClass419_long G :=
Iff.intro (CC419_implies_long G) (CC419_implied_by_long G)

theorem CC420_implies_long (G : Type*) [Magma G] (h : ConjunctionClass420 G) : ConjunctionClass420_long G := by
  obtain ⟨eq4369, eq4512⟩ := h
  have eq1 := Equation4369_4512_implies_Equation1 G eq4369 eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4290, eq4369, eq4512⟩

theorem CC420_implied_by_long (G : Type*) [Magma G] : ConjunctionClass420_long G -> ConjunctionClass420 G :=
fun ⟨_, _, h4369, h4512⟩ => ⟨h4369, h4512⟩

theorem CC420_equiv (G : Type*) [Magma G] : ConjunctionClass420 G <-> ConjunctionClass420_long G :=
Iff.intro (CC420_implies_long G) (CC420_implied_by_long G)

theorem CC421_implies_long (G : Type*) [Magma G] (h : ConjunctionClass421 G) : ConjunctionClass421_long G := by
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

theorem CC421_implied_by_long (G : Type*) [Magma G] : ConjunctionClass421_long G -> ConjunctionClass421 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h40, h4369, h4512⟩

theorem CC421_equiv (G : Type*) [Magma G] : ConjunctionClass421 G <-> ConjunctionClass421_long G :=
Iff.intro (CC421_implies_long G) (CC421_implied_by_long G)

theorem CC422_implies_long (G : Type*) [Magma G] (h : ConjunctionClass422 G) : ConjunctionClass422_long G := by
  obtain ⟨eq307, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  exact ⟨eq1, eq307, eq3253, eq4290, eq4369, eq4512⟩

theorem CC422_implied_by_long (G : Type*) [Magma G] : ConjunctionClass422_long G -> ConjunctionClass422 G :=
fun ⟨_, h307, _, _, h4369, h4512⟩ => ⟨h307, h4369, h4512⟩

theorem CC422_equiv (G : Type*) [Magma G] : ConjunctionClass422 G <-> ConjunctionClass422_long G :=
Iff.intro (CC422_implies_long G) (CC422_implied_by_long G)

theorem CC423_implies_long (G : Type*) [Magma G] (h : ConjunctionClass423 G) : ConjunctionClass423_long G := by
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

theorem CC423_implied_by_long (G : Type*) [Magma G] : ConjunctionClass423_long G -> ConjunctionClass423 G :=
fun ⟨_, h40, h307, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h40, h307, h4369, h4512⟩

theorem CC423_equiv (G : Type*) [Magma G] : ConjunctionClass423 G <-> ConjunctionClass423_long G :=
Iff.intro (CC423_implies_long G) (CC423_implied_by_long G)

theorem CC424_implies_long (G : Type*) [Magma G] (h : ConjunctionClass424 G) : ConjunctionClass424_long G := by
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

theorem CC424_implied_by_long (G : Type*) [Magma G] : ConjunctionClass424_long G -> ConjunctionClass424 G :=
fun ⟨_, _, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h309, h4369, h4512⟩

theorem CC424_equiv (G : Type*) [Magma G] : ConjunctionClass424 G <-> ConjunctionClass424_long G :=
Iff.intro (CC424_implies_long G) (CC424_implied_by_long G)

theorem CC425_implies_long (G : Type*) [Magma G] (h : ConjunctionClass425 G) : ConjunctionClass425_long G := by
  obtain ⟨eq3253, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq3253, eq4290, eq4369, eq4512⟩

theorem CC425_implied_by_long (G : Type*) [Magma G] : ConjunctionClass425_long G -> ConjunctionClass425 G :=
fun ⟨_, h3253, _, h4369, h4512⟩ => ⟨h3253, h4369, h4512⟩

theorem CC425_equiv (G : Type*) [Magma G] : ConjunctionClass425 G <-> ConjunctionClass425_long G :=
Iff.intro (CC425_implies_long G) (CC425_implied_by_long G)

theorem CC426_implies_long (G : Type*) [Magma G] (h : ConjunctionClass426 G) : ConjunctionClass426_long G := by
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

theorem CC426_implied_by_long (G : Type*) [Magma G] : ConjunctionClass426_long G -> ConjunctionClass426 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h3267, h4369, h4512⟩

theorem CC426_equiv (G : Type*) [Magma G] : ConjunctionClass426 G <-> ConjunctionClass426_long G :=
Iff.intro (CC426_implies_long G) (CC426_implied_by_long G)

theorem CC427_implies_long (G : Type*) [Magma G] (h : ConjunctionClass427 G) : ConjunctionClass427_long G := by
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

theorem CC427_implied_by_long (G : Type*) [Magma G] : ConjunctionClass427_long G -> ConjunctionClass427 G :=
fun ⟨_, _, _, _, h309, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h309, h3267, h4369, h4512⟩

theorem CC427_equiv (G : Type*) [Magma G] : ConjunctionClass427 G <-> ConjunctionClass427_long G :=
Iff.intro (CC427_implies_long G) (CC427_implied_by_long G)

theorem CC428_implies_long (G : Type*) [Magma G] (h : ConjunctionClass428 G) : ConjunctionClass428_long G := by
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

theorem CC428_implied_by_long (G : Type*) [Magma G] : ConjunctionClass428_long G -> ConjunctionClass428 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4268, h4369, h4512⟩

theorem CC428_equiv (G : Type*) [Magma G] : ConjunctionClass428 G <-> ConjunctionClass428_long G :=
Iff.intro (CC428_implies_long G) (CC428_implied_by_long G)

theorem CC429_implies_long (G : Type*) [Magma G] (h : ConjunctionClass429 G) : ConjunctionClass429_long G := by
  obtain ⟨eq4269, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4273 := Equation4269_4290_4512_implies_Equation4273 G eq4269 eq4290 eq4512
  have eq4279 := Equation4269_4273_4512_implies_Equation4279 G eq4269 eq4273 eq4512
  have eq4276 := Equation4279_4512_implies_Equation4276 G eq4279 eq4512
  have eq4321 := Equation4279_4512_implies_Equation4321 G eq4279 eq4512
  exact ⟨eq1, eq4269, eq4273, eq4276, eq4279, eq4290, eq4321, eq4369, eq4512⟩

theorem CC429_implied_by_long (G : Type*) [Magma G] : ConjunctionClass429_long G -> ConjunctionClass429 G :=
fun ⟨_, h4269, _, _, _, _, _, h4369, h4512⟩ => ⟨h4269, h4369, h4512⟩

theorem CC429_equiv (G : Type*) [Magma G] : ConjunctionClass429 G <-> ConjunctionClass429_long G :=
Iff.intro (CC429_implies_long G) (CC429_implied_by_long G)

theorem CC430_implies_long (G : Type*) [Magma G] (h : ConjunctionClass430 G) : ConjunctionClass430_long G := by
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

theorem CC430_implied_by_long (G : Type*) [Magma G] : ConjunctionClass430_long G -> ConjunctionClass430 G :=
fun ⟨_, h4268, h4269, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4268, h4269, h4369, h4512⟩

theorem CC430_equiv (G : Type*) [Magma G] : ConjunctionClass430 G <-> ConjunctionClass430_long G :=
Iff.intro (CC430_implies_long G) (CC430_implied_by_long G)

theorem CC431_implies_long (G : Type*) [Magma G] (h : ConjunctionClass431 G) : ConjunctionClass431_long G := by
  obtain ⟨eq4270, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4275 := Equation4270_4290_4512_implies_Equation4275 G eq4270 eq4290 eq4512
  have eq4297 := Equation4270_4275_4512_implies_Equation4297 G eq4270 eq4275 eq4512
  exact ⟨eq1, eq4270, eq4275, eq4290, eq4297, eq4369, eq4512⟩

theorem CC431_implied_by_long (G : Type*) [Magma G] : ConjunctionClass431_long G -> ConjunctionClass431 G :=
fun ⟨_, h4270, _, _, _, h4369, h4512⟩ => ⟨h4270, h4369, h4512⟩

theorem CC431_equiv (G : Type*) [Magma G] : ConjunctionClass431 G <-> ConjunctionClass431_long G :=
Iff.intro (CC431_implies_long G) (CC431_implied_by_long G)

theorem CC432_implies_long (G : Type*) [Magma G] (h : ConjunctionClass432 G) : ConjunctionClass432_long G := by
  obtain ⟨eq4273, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4273, eq4290, eq4369, eq4512⟩

theorem CC432_implied_by_long (G : Type*) [Magma G] : ConjunctionClass432_long G -> ConjunctionClass432 G :=
fun ⟨_, h4273, _, h4369, h4512⟩ => ⟨h4273, h4369, h4512⟩

theorem CC432_equiv (G : Type*) [Magma G] : ConjunctionClass432 G <-> ConjunctionClass432_long G :=
Iff.intro (CC432_implies_long G) (CC432_implied_by_long G)

theorem CC433_implies_long (G : Type*) [Magma G] (h : ConjunctionClass433 G) : ConjunctionClass433_long G := by
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

theorem CC433_implied_by_long (G : Type*) [Magma G] : ConjunctionClass433_long G -> ConjunctionClass433 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, h4273, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h40, h4273, h4369, h4512⟩

theorem CC433_equiv (G : Type*) [Magma G] : ConjunctionClass433 G <-> ConjunctionClass433_long G :=
Iff.intro (CC433_implies_long G) (CC433_implied_by_long G)

theorem CC434_implies_long (G : Type*) [Magma G] (h : ConjunctionClass434 G) : ConjunctionClass434_long G := by
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

theorem CC434_implied_by_long (G : Type*) [Magma G] : ConjunctionClass434_long G -> ConjunctionClass434 G :=
fun ⟨_, h4270, h4273, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4270, h4273, h4369, h4512⟩

theorem CC434_equiv (G : Type*) [Magma G] : ConjunctionClass434 G <-> ConjunctionClass434_long G :=
Iff.intro (CC434_implies_long G) (CC434_implied_by_long G)

theorem CC435_implies_long (G : Type*) [Magma G] (h : ConjunctionClass435 G) : ConjunctionClass435_long G := by
  obtain ⟨eq4276, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4276, eq4290, eq4369, eq4512⟩

theorem CC435_implied_by_long (G : Type*) [Magma G] : ConjunctionClass435_long G -> ConjunctionClass435 G :=
fun ⟨_, h4276, _, h4369, h4512⟩ => ⟨h4276, h4369, h4512⟩

theorem CC435_equiv (G : Type*) [Magma G] : ConjunctionClass435 G <-> ConjunctionClass435_long G :=
Iff.intro (CC435_implies_long G) (CC435_implied_by_long G)

theorem CC436_implies_long (G : Type*) [Magma G] (h : ConjunctionClass436 G) : ConjunctionClass436_long G := by
  obtain ⟨eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem CC436_implied_by_long (G : Type*) [Magma G] : ConjunctionClass436_long G -> ConjunctionClass436 G :=
fun ⟨_, h4283, _, _, h4369, h4512⟩ => ⟨h4283, h4369, h4512⟩

theorem CC436_equiv (G : Type*) [Magma G] : ConjunctionClass436 G <-> ConjunctionClass436_long G :=
Iff.intro (CC436_implies_long G) (CC436_implied_by_long G)

theorem CC437_implies_long (G : Type*) [Magma G] (h : ConjunctionClass437 G) : ConjunctionClass437_long G := by
  obtain ⟨eq307, eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem CC437_implied_by_long (G : Type*) [Magma G] : ConjunctionClass437_long G -> ConjunctionClass437 G :=
fun ⟨_, h307, _, h4283, _, _, h4369, h4512⟩ => ⟨h307, h4283, h4369, h4512⟩

theorem CC437_equiv (G : Type*) [Magma G] : ConjunctionClass437 G <-> ConjunctionClass437_long G :=
Iff.intro (CC437_implies_long G) (CC437_implied_by_long G)

theorem CC438_implies_long (G : Type*) [Magma G] (h : ConjunctionClass438 G) : ConjunctionClass438_long G := by
  obtain ⟨eq3253, eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq3253, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem CC438_implied_by_long (G : Type*) [Magma G] : ConjunctionClass438_long G -> ConjunctionClass438 G :=
fun ⟨_, h3253, h4283, _, _, h4369, h4512⟩ => ⟨h3253, h4283, h4369, h4512⟩

theorem CC438_equiv (G : Type*) [Magma G] : ConjunctionClass438 G <-> ConjunctionClass438_long G :=
Iff.intro (CC438_implies_long G) (CC438_implied_by_long G)

theorem CC439_implies_long (G : Type*) [Magma G] (h : ConjunctionClass439 G) : ConjunctionClass439_long G := by
  obtain ⟨eq4276, eq4283, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4320 := Equation4283_4290_4512_implies_Equation4320 G eq4283 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4283, eq4290, eq4320, eq4369, eq4512⟩

theorem CC439_implied_by_long (G : Type*) [Magma G] : ConjunctionClass439_long G -> ConjunctionClass439 G :=
fun ⟨_, h4276, h4283, _, _, h4369, h4512⟩ => ⟨h4276, h4283, h4369, h4512⟩

theorem CC439_equiv (G : Type*) [Magma G] : ConjunctionClass439 G <-> ConjunctionClass439_long G :=
Iff.intro (CC439_implies_long G) (CC439_implied_by_long G)

theorem CC440_implies_long (G : Type*) [Magma G] (h : ConjunctionClass440 G) : ConjunctionClass440_long G := by
  obtain ⟨eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4343, eq4369, eq4512⟩

theorem CC440_implied_by_long (G : Type*) [Magma G] : ConjunctionClass440_long G -> ConjunctionClass440 G :=
fun ⟨_, h4284, _, _, _, h4369, h4512⟩ => ⟨h4284, h4369, h4512⟩

theorem CC440_equiv (G : Type*) [Magma G] : ConjunctionClass440 G <-> ConjunctionClass440_long G :=
Iff.intro (CC440_implies_long G) (CC440_implied_by_long G)

theorem CC441_implies_long (G : Type*) [Magma G] (h : ConjunctionClass441 G) : ConjunctionClass441_long G := by
  obtain ⟨eq307, eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4343, eq4369, eq4512⟩

theorem CC441_implied_by_long (G : Type*) [Magma G] : ConjunctionClass441_long G -> ConjunctionClass441 G :=
fun ⟨_, h307, _, h4284, _, _, _, h4369, h4512⟩ => ⟨h307, h4284, h4369, h4512⟩

theorem CC441_equiv (G : Type*) [Magma G] : ConjunctionClass441 G <-> ConjunctionClass441_long G :=
Iff.intro (CC441_implies_long G) (CC441_implied_by_long G)

theorem CC442_implies_long (G : Type*) [Magma G] (h : ConjunctionClass442 G) : ConjunctionClass442_long G := by
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

theorem CC442_implied_by_long (G : Type*) [Magma G] : ConjunctionClass442_long G -> ConjunctionClass442 G :=
fun ⟨_, h4269, _, _, _, h4284, _, _, _, _, h4369, h4512⟩ => ⟨h4269, h4284, h4369, h4512⟩

theorem CC442_equiv (G : Type*) [Magma G] : ConjunctionClass442 G <-> ConjunctionClass442_long G :=
Iff.intro (CC442_implies_long G) (CC442_implied_by_long G)

theorem CC443_implies_long (G : Type*) [Magma G] (h : ConjunctionClass443 G) : ConjunctionClass443_long G := by
  obtain ⟨eq4276, eq4284, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4343, eq4369, eq4512⟩

theorem CC443_implied_by_long (G : Type*) [Magma G] : ConjunctionClass443_long G -> ConjunctionClass443 G :=
fun ⟨_, h4276, h4284, _, _, _, h4369, h4512⟩ => ⟨h4276, h4284, h4369, h4512⟩

theorem CC443_equiv (G : Type*) [Magma G] : ConjunctionClass443 G <-> ConjunctionClass443_long G :=
Iff.intro (CC443_implies_long G) (CC443_implied_by_long G)

theorem CC444_implies_long (G : Type*) [Magma G] (h : ConjunctionClass444 G) : ConjunctionClass444_long G := by
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

theorem CC444_implied_by_long (G : Type*) [Magma G] : ConjunctionClass444_long G -> ConjunctionClass444 G :=
fun ⟨_, h4283, h4284, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4283, h4284, h4369, h4512⟩

theorem CC444_equiv (G : Type*) [Magma G] : ConjunctionClass444 G <-> ConjunctionClass444_long G :=
Iff.intro (CC444_implies_long G) (CC444_implied_by_long G)

theorem CC445_implies_long (G : Type*) [Magma G] (h : ConjunctionClass445 G) : ConjunctionClass445_long G := by
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

theorem CC445_implied_by_long (G : Type*) [Magma G] : ConjunctionClass445_long G -> ConjunctionClass445 G :=
fun ⟨_, h307, _, h4283, h4284, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h307, h4283, h4284, h4369, h4512⟩

theorem CC445_equiv (G : Type*) [Magma G] : ConjunctionClass445 G <-> ConjunctionClass445_long G :=
Iff.intro (CC445_implies_long G) (CC445_implied_by_long G)

theorem CC446_implies_long (G : Type*) [Magma G] (h : ConjunctionClass446 G) : ConjunctionClass446_long G := by
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

theorem CC446_implied_by_long (G : Type*) [Magma G] : ConjunctionClass446_long G -> ConjunctionClass446 G :=
fun ⟨_, h4276, h4283, h4284, _, _, _, _, _, _, _, h4369, h4512⟩ => ⟨h4276, h4283, h4284, h4369, h4512⟩

theorem CC446_equiv (G : Type*) [Magma G] : ConjunctionClass446 G <-> ConjunctionClass446_long G :=
Iff.intro (CC446_implies_long G) (CC446_implied_by_long G)

theorem CC447_implies_long (G : Type*) [Magma G] (h : ConjunctionClass447 G) : ConjunctionClass447_long G := by
  obtain ⟨eq4291, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  exact ⟨eq1, eq4290, eq4291, eq4314, eq4369, eq4512⟩

theorem CC447_implied_by_long (G : Type*) [Magma G] : ConjunctionClass447_long G -> ConjunctionClass447 G :=
fun ⟨_, _, h4291, _, h4369, h4512⟩ => ⟨h4291, h4369, h4512⟩

theorem CC447_equiv (G : Type*) [Magma G] : ConjunctionClass447 G <-> ConjunctionClass447_long G :=
Iff.intro (CC447_implies_long G) (CC447_implied_by_long G)

theorem CC448_implies_long (G : Type*) [Magma G] (h : ConjunctionClass448 G) : ConjunctionClass448_long G := by
  obtain ⟨eq4276, eq4291, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4314 := Equation4290_4291_4512_implies_Equation4314 G eq4290 eq4291 eq4512
  exact ⟨eq1, eq4276, eq4290, eq4291, eq4314, eq4369, eq4512⟩

theorem CC448_implied_by_long (G : Type*) [Magma G] : ConjunctionClass448_long G -> ConjunctionClass448 G :=
fun ⟨_, h4276, _, h4291, _, h4369, h4512⟩ => ⟨h4276, h4291, h4369, h4512⟩

theorem CC448_equiv (G : Type*) [Magma G] : ConjunctionClass448 G <-> ConjunctionClass448_long G :=
Iff.intro (CC448_implies_long G) (CC448_implied_by_long G)

theorem CC449_implies_long (G : Type*) [Magma G] (h : ConjunctionClass449 G) : ConjunctionClass449_long G := by
  obtain ⟨eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4290, eq4321, eq4369, eq4512⟩

theorem CC449_implied_by_long (G : Type*) [Magma G] : ConjunctionClass449_long G -> ConjunctionClass449 G :=
fun ⟨_, _, h4321, h4369, h4512⟩ => ⟨h4321, h4369, h4512⟩

theorem CC449_equiv (G : Type*) [Magma G] : ConjunctionClass449 G <-> ConjunctionClass449_long G :=
Iff.intro (CC449_implies_long G) (CC449_implied_by_long G)

theorem CC450_implies_long (G : Type*) [Magma G] (h : ConjunctionClass450 G) : ConjunctionClass450_long G := by
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

theorem CC450_implied_by_long (G : Type*) [Magma G] : ConjunctionClass450_long G -> ConjunctionClass450 G :=
fun ⟨_, h40, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h40, h4321, h4369, h4512⟩

theorem CC450_equiv (G : Type*) [Magma G] : ConjunctionClass450 G <-> ConjunctionClass450_long G :=
Iff.intro (CC450_implies_long G) (CC450_implied_by_long G)

theorem CC451_implies_long (G : Type*) [Magma G] (h : ConjunctionClass451 G) : ConjunctionClass451_long G := by
  obtain ⟨eq307, eq4321, eq4369, eq4512⟩ := h
  have eq4293 := Equation307_4321_4369_4512_implies_Equation4293 G eq307 eq4321 eq4369 eq4512
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq3253 := Equation307_4512_implies_Equation3253 G eq307 eq4512
  have eq4284 := Equation4290_4293_4512_implies_Equation4284 G eq4290 eq4293 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq307, eq3253, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem CC451_implied_by_long (G : Type*) [Magma G] : ConjunctionClass451_long G -> ConjunctionClass451 G :=
fun ⟨_, h307, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h307, h4321, h4369, h4512⟩

theorem CC451_equiv (G : Type*) [Magma G] : ConjunctionClass451 G <-> ConjunctionClass451_long G :=
Iff.intro (CC451_implies_long G) (CC451_implied_by_long G)

theorem CC452_implies_long (G : Type*) [Magma G] (h : ConjunctionClass452 G) : ConjunctionClass452_long G := by
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

theorem CC452_implied_by_long (G : Type*) [Magma G] : ConjunctionClass452_long G -> ConjunctionClass452 G :=
fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3267, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h3267, h4321, h4369, h4512⟩

theorem CC452_equiv (G : Type*) [Magma G] : ConjunctionClass452 G <-> ConjunctionClass452_long G :=
Iff.intro (CC452_implies_long G) (CC452_implied_by_long G)

theorem CC453_implies_long (G : Type*) [Magma G] (h : ConjunctionClass453 G) : ConjunctionClass453_long G := by
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

theorem CC453_implied_by_long (G : Type*) [Magma G] : ConjunctionClass453_long G -> ConjunctionClass453 G :=
fun ⟨_, h4268, _, _, _, _, _, _, _, _, _, _, _, _, _, h4321, _, h4369, h4512⟩ => ⟨h4268, h4321, h4369, h4512⟩

theorem CC453_equiv (G : Type*) [Magma G] : ConjunctionClass453 G <-> ConjunctionClass453_long G :=
Iff.intro (CC453_implies_long G) (CC453_implied_by_long G)

theorem CC454_implies_long (G : Type*) [Magma G] (h : ConjunctionClass454 G) : ConjunctionClass454_long G := by
  obtain ⟨eq4276, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  exact ⟨eq1, eq4276, eq4290, eq4321, eq4369, eq4512⟩

theorem CC454_implied_by_long (G : Type*) [Magma G] : ConjunctionClass454_long G -> ConjunctionClass454 G :=
fun ⟨_, h4276, _, h4321, h4369, h4512⟩ => ⟨h4276, h4321, h4369, h4512⟩

theorem CC454_equiv (G : Type*) [Magma G] : ConjunctionClass454 G <-> ConjunctionClass454_long G :=
Iff.intro (CC454_implies_long G) (CC454_implied_by_long G)

theorem CC455_implies_long (G : Type*) [Magma G] (h : ConjunctionClass455 G) : ConjunctionClass455_long G := by
  obtain ⟨eq4284, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem CC455_implied_by_long (G : Type*) [Magma G] : ConjunctionClass455_long G -> ConjunctionClass455 G :=
fun ⟨_, h4284, _, _, h4321, _, h4369, h4512⟩ => ⟨h4284, h4321, h4369, h4512⟩

theorem CC455_equiv (G : Type*) [Magma G] : ConjunctionClass455 G <-> ConjunctionClass455_long G :=
Iff.intro (CC455_implies_long G) (CC455_implied_by_long G)

theorem CC456_implies_long (G : Type*) [Magma G] (h : ConjunctionClass456 G) : ConjunctionClass456_long G := by
  obtain ⟨eq4276, eq4284, eq4321, eq4369, eq4512⟩ := h
  have eq1 := Equation4512_implies_Equation1 G eq4512
  have eq4290 := Equation4369_4512_implies_Equation4290 G eq4369 eq4512
  have eq4293 := Equation4284_4290_4512_implies_Equation4293 G eq4284 eq4290 eq4512
  have eq4343 := Equation4284_4290_4512_implies_Equation4343 G eq4284 eq4290 eq4512
  exact ⟨eq1, eq4276, eq4284, eq4290, eq4293, eq4321, eq4343, eq4369, eq4512⟩

theorem CC456_implied_by_long (G : Type*) [Magma G] : ConjunctionClass456_long G -> ConjunctionClass456 G :=
fun ⟨_, h4276, h4284, _, _, h4321, _, h4369, h4512⟩ => ⟨h4276, h4284, h4321, h4369, h4512⟩

theorem CC456_equiv (G : Type*) [Magma G] : ConjunctionClass456 G <-> ConjunctionClass456_long G :=
Iff.intro (CC456_implies_long G) (CC456_implied_by_long G)

