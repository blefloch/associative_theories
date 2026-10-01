import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model54_op := finOpTable "[[1,2,0,5,12,9,20,13,4,3,18,19,8,15,6,7,10,11,16,17,14,23,25,26,22,24,21],[2,0,1,9,8,3,14,15,12,5,16,17,4,7,20,13,18,19,10,11,6,26,24,21,25,22,23],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26],[7,11,3,4,2,14,1,10,23,18,0,6,24,8,21,20,26,12,22,16,25,5,9,13,17,15,19],[10,6,4,2,3,21,11,0,13,22,7,1,17,23,5,25,19,24,9,26,15,14,18,8,12,20,16],[13,19,5,12,0,6,2,18,26,16,1,20,22,4,23,14,21,8,25,10,24,9,3,15,11,7,17],[4,10,6,22,13,2,5,25,17,21,19,24,3,0,15,23,9,26,7,1,11,16,12,14,20,18,8],[11,3,7,14,24,18,25,8,2,4,22,16,23,20,1,10,0,6,26,12,21,13,15,19,9,17,5],[16,14,8,1,9,26,17,2,7,24,15,0,19,21,3,22,11,25,5,23,13,20,10,12,4,6,18],[15,17,9,8,1,20,0,16,21,10,2,14,25,12,26,6,23,4,24,18,22,3,5,7,19,13,11],[6,4,10,21,17,22,15,23,3,2,9,26,13,25,11,0,7,1,19,24,5,8,20,16,18,12,14],[3,7,11,18,23,4,21,20,24,14,26,12,2,10,25,8,22,16,0,6,1,19,17,5,15,9,13],[18,20,12,0,5,23,19,1,15,25,13,2,11,26,9,24,17,22,3,21,7,6,16,4,8,14,10],[19,5,13,6,22,16,24,4,0,12,25,10,26,14,2,18,1,20,21,8,23,15,7,17,3,11,9],[8,16,14,24,7,1,3,22,19,26,11,25,9,2,13,21,5,23,15,0,17,18,4,20,6,10,12],[17,9,15,20,25,10,22,12,1,8,24,18,21,6,0,16,2,14,23,4,26,7,13,11,5,19,3],[14,8,16,26,19,24,13,21,9,1,5,23,7,22,17,2,15,0,11,25,3,12,6,18,10,4,20],[9,15,17,10,21,8,26,6,25,20,23,4,1,16,22,12,24,18,2,14,0,11,19,3,13,5,7],[20,12,18,23,11,25,7,26,5,0,3,21,15,24,19,1,13,2,17,22,9,4,14,10,16,8,6],[5,13,19,16,26,12,23,14,22,6,21,8,0,18,24,4,25,10,1,20,2,17,11,9,7,3,15],[12,18,20,25,15,0,9,24,11,23,17,22,5,1,7,26,3,21,13,2,19,10,8,6,14,16,4],[23,26,21,17,10,11,4,9,16,19,6,15,18,3,8,5,14,13,20,7,12,22,2,25,1,0,24],[25,24,22,13,6,15,10,19,14,7,4,5,20,17,16,11,8,3,12,9,18,2,21,0,26,23,1],[26,21,23,11,18,19,12,3,10,17,20,7,16,5,4,9,6,15,14,13,8,25,0,24,2,1,22],[22,25,24,7,14,13,16,11,20,15,8,3,6,19,18,17,12,9,4,5,10,1,26,2,23,21,0],[24,22,25,15,20,7,18,17,6,13,12,9,14,11,10,19,4,5,8,3,16,0,23,1,21,26,2],[21,23,26,19,16,17,8,5,18,11,14,13,10,9,12,3,20,7,6,15,4,24,1,22,0,2,25]]"
private def model54 : Magma (Fin 27) where op := model54_op
private instance : Magma (Fin 27) := model54

private theorem model54_eq1 : Equation1 (Fin 27) := by decideFin!
private theorem not_model54_eq2 : Not (Equation2 (Fin 27)) := by decideFin!
private theorem not_model54_eq3 : Not (Equation3 (Fin 27)) := by decideFin!
private theorem not_model54_eq4 : Not (Equation4 (Fin 27)) := by decideFin!
private theorem not_model54_eq5 : Not (Equation5 (Fin 27)) := by decideFin!
private theorem not_model54_eq8 : Not (Equation8 (Fin 27)) := by decideFin!
private theorem not_model54_eq10 : Not (Equation10 (Fin 27)) := by decideFin!
private theorem not_model54_eq11 : Not (Equation11 (Fin 27)) := by decideFin!
private theorem not_model54_eq14 : Not (Equation14 (Fin 27)) := by decideFin!
private theorem not_model54_eq16 : Not (Equation16 (Fin 27)) := by decideFin!
private theorem not_model54_eq38 : Not (Equation38 (Fin 27)) := by decideFin!
private theorem not_model54_eq39 : Not (Equation39 (Fin 27)) := by decideFin!
private theorem not_model54_eq40 : Not (Equation40 (Fin 27)) := by decideFin!
private theorem not_model54_eq41 : Not (Equation41 (Fin 27)) := by decideFin!
private theorem not_model54_eq43 : Not (Equation43 (Fin 27)) := by decideFin!
private theorem model54_eq47 : Equation47 (Fin 27) := by decideFin!
private theorem model54_eq56 : Equation56 (Fin 27) := by decideFin!
private theorem not_model54_eq66 : Not (Equation66 (Fin 27)) := by decideFin!
private theorem model54_eq75 : Equation75 (Fin 27) := by decideFin!
private theorem not_model54_eq307 : Not (Equation307 (Fin 27)) := by decideFin!
private theorem not_model54_eq308 : Not (Equation308 (Fin 27)) := by decideFin!
private theorem not_model54_eq309 : Not (Equation309 (Fin 27)) := by decideFin!
private theorem not_model54_eq310 : Not (Equation310 (Fin 27)) := by decideFin!
private theorem not_model54_eq311 : Not (Equation311 (Fin 27)) := by decideFin!
private theorem not_model54_eq312 : Not (Equation312 (Fin 27)) := by decideFin!
private theorem not_model54_eq313 : Not (Equation313 (Fin 27)) := by decideFin!
private theorem not_model54_eq314 : Not (Equation314 (Fin 27)) := by decideFin!
private theorem not_model54_eq315 : Not (Equation315 (Fin 27)) := by decideFin!
private theorem not_model54_eq316 : Not (Equation316 (Fin 27)) := by decideFin!
private theorem not_model54_eq318 : Not (Equation318 (Fin 27)) := by decideFin!
private theorem not_model54_eq323 : Not (Equation323 (Fin 27)) := by decideFin!
private theorem not_model54_eq325 : Not (Equation325 (Fin 27)) := by decideFin!
private theorem not_model54_eq326 : Not (Equation326 (Fin 27)) := by decideFin!
private theorem not_model54_eq327 : Not (Equation327 (Fin 27)) := by decideFin!
private theorem not_model54_eq329 : Not (Equation329 (Fin 27)) := by decideFin!
private theorem not_model54_eq332 : Not (Equation332 (Fin 27)) := by decideFin!
private theorem not_model54_eq333 : Not (Equation333 (Fin 27)) := by decideFin!
private theorem not_model54_eq343 : Not (Equation343 (Fin 27)) := by decideFin!
private theorem not_model54_eq411 : Not (Equation411 (Fin 27)) := by decideFin!
private theorem not_model54_eq419 : Not (Equation419 (Fin 27)) := by decideFin!
private theorem not_model54_eq429 : Not (Equation429 (Fin 27)) := by decideFin!
private theorem not_model54_eq440 : Not (Equation440 (Fin 27)) := by decideFin!
private theorem not_model54_eq477 : Not (Equation477 (Fin 27)) := by decideFin!
private theorem not_model54_eq504 : Not (Equation504 (Fin 27)) := by decideFin!
private theorem not_model54_eq513 : Not (Equation513 (Fin 27)) := by decideFin!
private theorem not_model54_eq3253 : Not (Equation3253 (Fin 27)) := by decideFin!
private theorem not_model54_eq3255 : Not (Equation3255 (Fin 27)) := by decideFin!
private theorem not_model54_eq3256 : Not (Equation3256 (Fin 27)) := by decideFin!
private theorem not_model54_eq3258 : Not (Equation3258 (Fin 27)) := by decideFin!
private theorem not_model54_eq3259 : Not (Equation3259 (Fin 27)) := by decideFin!
private theorem not_model54_eq3260 : Not (Equation3260 (Fin 27)) := by decideFin!
private theorem not_model54_eq3261 : Not (Equation3261 (Fin 27)) := by decideFin!
private theorem not_model54_eq3264 : Not (Equation3264 (Fin 27)) := by decideFin!
private theorem not_model54_eq3265 : Not (Equation3265 (Fin 27)) := by decideFin!
private theorem not_model54_eq3267 : Not (Equation3267 (Fin 27)) := by decideFin!
private theorem not_model54_eq3271 : Not (Equation3271 (Fin 27)) := by decideFin!
private theorem not_model54_eq3273 : Not (Equation3273 (Fin 27)) := by decideFin!
private theorem not_model54_eq3274 : Not (Equation3274 (Fin 27)) := by decideFin!
private theorem not_model54_eq3275 : Not (Equation3275 (Fin 27)) := by decideFin!
private theorem not_model54_eq3277 : Not (Equation3277 (Fin 27)) := by decideFin!
private theorem not_model54_eq3278 : Not (Equation3278 (Fin 27)) := by decideFin!
private theorem not_model54_eq3290 : Not (Equation3290 (Fin 27)) := by decideFin!
private theorem not_model54_eq3292 : Not (Equation3292 (Fin 27)) := by decideFin!
private theorem not_model54_eq3300 : Not (Equation3300 (Fin 27)) := by decideFin!
private theorem not_model54_eq3306 : Not (Equation3306 (Fin 27)) := by decideFin!
private theorem not_model54_eq3308 : Not (Equation3308 (Fin 27)) := by decideFin!
private theorem not_model54_eq3309 : Not (Equation3309 (Fin 27)) := by decideFin!
private theorem not_model54_eq3315 : Not (Equation3315 (Fin 27)) := by decideFin!
private theorem not_model54_eq3316 : Not (Equation3316 (Fin 27)) := by decideFin!
private theorem not_model54_eq3319 : Not (Equation3319 (Fin 27)) := by decideFin!
private theorem not_model54_eq3322 : Not (Equation3322 (Fin 27)) := by decideFin!
private theorem not_model54_eq3323 : Not (Equation3323 (Fin 27)) := by decideFin!
private theorem not_model54_eq3326 : Not (Equation3326 (Fin 27)) := by decideFin!
private theorem not_model54_eq3331 : Not (Equation3331 (Fin 27)) := by decideFin!
private theorem not_model54_eq3334 : Not (Equation3334 (Fin 27)) := by decideFin!
private theorem not_model54_eq3342 : Not (Equation3342 (Fin 27)) := by decideFin!
private theorem not_model54_eq3346 : Not (Equation3346 (Fin 27)) := by decideFin!
private theorem not_model54_eq3350 : Not (Equation3350 (Fin 27)) := by decideFin!
private theorem not_model54_eq3353 : Not (Equation3353 (Fin 27)) := by decideFin!
private theorem not_model54_eq3388 : Not (Equation3388 (Fin 27)) := by decideFin!
private theorem not_model54_eq3414 : Not (Equation3414 (Fin 27)) := by decideFin!
private theorem not_model54_eq4268 : Not (Equation4268 (Fin 27)) := by decideFin!
private theorem not_model54_eq4269 : Not (Equation4269 (Fin 27)) := by decideFin!
private theorem not_model54_eq4270 : Not (Equation4270 (Fin 27)) := by decideFin!
private theorem not_model54_eq4271 : Not (Equation4271 (Fin 27)) := by decideFin!
private theorem not_model54_eq4272 : Not (Equation4272 (Fin 27)) := by decideFin!
private theorem not_model54_eq4273 : Not (Equation4273 (Fin 27)) := by decideFin!
private theorem not_model54_eq4274 : Not (Equation4274 (Fin 27)) := by decideFin!
private theorem not_model54_eq4275 : Not (Equation4275 (Fin 27)) := by decideFin!
private theorem model54_eq4276 : Equation4276 (Fin 27) := by decideFin!
private theorem not_model54_eq4277 : Not (Equation4277 (Fin 27)) := by decideFin!
private theorem not_model54_eq4278 : Not (Equation4278 (Fin 27)) := by decideFin!
private theorem not_model54_eq4279 : Not (Equation4279 (Fin 27)) := by decideFin!
private theorem not_model54_eq4280 : Not (Equation4280 (Fin 27)) := by decideFin!
private theorem not_model54_eq4283 : Not (Equation4283 (Fin 27)) := by decideFin!
private theorem not_model54_eq4284 : Not (Equation4284 (Fin 27)) := by decideFin!
private theorem not_model54_eq4286 : Not (Equation4286 (Fin 27)) := by decideFin!
private theorem not_model54_eq4287 : Not (Equation4287 (Fin 27)) := by decideFin!
private theorem not_model54_eq4288 : Not (Equation4288 (Fin 27)) := by decideFin!
private theorem not_model54_eq4290 : Not (Equation4290 (Fin 27)) := by decideFin!
private theorem not_model54_eq4291 : Not (Equation4291 (Fin 27)) := by decideFin!
private theorem not_model54_eq4293 : Not (Equation4293 (Fin 27)) := by decideFin!
private theorem not_model54_eq4296 : Not (Equation4296 (Fin 27)) := by decideFin!
private theorem not_model54_eq4297 : Not (Equation4297 (Fin 27)) := by decideFin!
private theorem not_model54_eq4299 : Not (Equation4299 (Fin 27)) := by decideFin!
private theorem not_model54_eq4300 : Not (Equation4300 (Fin 27)) := by decideFin!
private theorem not_model54_eq4301 : Not (Equation4301 (Fin 27)) := by decideFin!
private theorem not_model54_eq4304 : Not (Equation4304 (Fin 27)) := by decideFin!
private theorem not_model54_eq4305 : Not (Equation4305 (Fin 27)) := by decideFin!
private theorem not_model54_eq4314 : Not (Equation4314 (Fin 27)) := by decideFin!
private theorem not_model54_eq4315 : Not (Equation4315 (Fin 27)) := by decideFin!
private theorem not_model54_eq4318 : Not (Equation4318 (Fin 27)) := by decideFin!
private theorem not_model54_eq4320 : Not (Equation4320 (Fin 27)) := by decideFin!
private theorem not_model54_eq4321 : Not (Equation4321 (Fin 27)) := by decideFin!
private theorem not_model54_eq4325 : Not (Equation4325 (Fin 27)) := by decideFin!
private theorem not_model54_eq4327 : Not (Equation4327 (Fin 27)) := by decideFin!
private theorem not_model54_eq4331 : Not (Equation4331 (Fin 27)) := by decideFin!
private theorem not_model54_eq4343 : Not (Equation4343 (Fin 27)) := by decideFin!
private theorem not_model54_eq4358 : Not (Equation4358 (Fin 27)) := by decideFin!
private theorem not_model54_eq4362 : Not (Equation4362 (Fin 27)) := by decideFin!
private theorem not_model54_eq4364 : Not (Equation4364 (Fin 27)) := by decideFin!
private theorem not_model54_eq4369 : Not (Equation4369 (Fin 27)) := by decideFin!
private theorem model54_eq4512 : Equation4512 (Fin 27) := by decideFin!

theorem model54_at1 : AssociativeTheory1 (Fin 27) :=
  model54_eq4512

theorem not_model54_at2 : Not (AssociativeTheory2 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq2

theorem not_model54_at3 : Not (AssociativeTheory3 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3

theorem not_model54_at4 : Not (AssociativeTheory4 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4

theorem not_model54_at5 : Not (AssociativeTheory5 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq5

theorem not_model54_at6 : Not (AssociativeTheory6 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at7 : Not (AssociativeTheory7 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq10

theorem not_model54_at8 : Not (AssociativeTheory8 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq11

theorem not_model54_at9 : Not (AssociativeTheory9 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq14

theorem not_model54_at10 : Not (AssociativeTheory10 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq16

theorem not_model54_at11 : Not (AssociativeTheory11 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq38

theorem not_model54_at12 : Not (AssociativeTheory12 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq39

theorem not_model54_at13 : Not (AssociativeTheory13 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq38

theorem not_model54_at14 : Not (AssociativeTheory14 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at15 : Not (AssociativeTheory15 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at16 : Not (AssociativeTheory16 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3

theorem not_model54_at17 : Not (AssociativeTheory17 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at18 : Not (AssociativeTheory18 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem model54_at19 : AssociativeTheory19 (Fin 27) :=
  ⟨model54_eq47, model54_eq4512⟩

theorem not_model54_at20 : Not (AssociativeTheory20 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem model54_at21 : AssociativeTheory21 (Fin 27) :=
  ⟨model54_eq56, model54_eq4512⟩

theorem not_model54_at22 : Not (AssociativeTheory22 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem model54_at23 : AssociativeTheory23 (Fin 27) :=
  ⟨model54_eq75, model54_eq4512⟩

theorem model54_at24 : AssociativeTheory24 (Fin 27) :=
  ⟨model54_eq56, model54_eq75, model54_eq4512⟩

theorem not_model54_at25 : Not (AssociativeTheory25 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at26 : Not (AssociativeTheory26 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at27 : Not (AssociativeTheory27 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at28 : Not (AssociativeTheory28 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at29 : Not (AssociativeTheory29 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq308

theorem not_model54_at30 : Not (AssociativeTheory30 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at31 : Not (AssociativeTheory31 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at32 : Not (AssociativeTheory32 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq308

theorem not_model54_at33 : Not (AssociativeTheory33 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq310

theorem not_model54_at34 : Not (AssociativeTheory34 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq311

theorem not_model54_at35 : Not (AssociativeTheory35 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at36 : Not (AssociativeTheory36 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at37 : Not (AssociativeTheory37 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq312

theorem not_model54_at38 : Not (AssociativeTheory38 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at39 : Not (AssociativeTheory39 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq315

theorem not_model54_at40 : Not (AssociativeTheory40 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq318

theorem not_model54_at41 : Not (AssociativeTheory41 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at42 : Not (AssociativeTheory42 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at43 : Not (AssociativeTheory43 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at44 : Not (AssociativeTheory44 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq312

theorem not_model54_at45 : Not (AssociativeTheory45 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq325

theorem not_model54_at46 : Not (AssociativeTheory46 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3

theorem not_model54_at47 : Not (AssociativeTheory47 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq308

theorem not_model54_at48 : Not (AssociativeTheory48 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at49 : Not (AssociativeTheory49 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at50 : Not (AssociativeTheory50 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at51 : Not (AssociativeTheory51 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq333

theorem not_model54_at52 : Not (AssociativeTheory52 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3

theorem not_model54_at53 : Not (AssociativeTheory53 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at54 : Not (AssociativeTheory54 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq411

theorem not_model54_at55 : Not (AssociativeTheory55 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at56 : Not (AssociativeTheory56 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq419

theorem not_model54_at57 : Not (AssociativeTheory57 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq429

theorem not_model54_at58 : Not (AssociativeTheory58 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq440

theorem not_model54_at59 : Not (AssociativeTheory59 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at60 : Not (AssociativeTheory60 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq504

theorem not_model54_at61 : Not (AssociativeTheory61 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq513

theorem not_model54_at62 : Not (AssociativeTheory62 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq440

theorem not_model54_at63 : Not (AssociativeTheory63 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at64 : Not (AssociativeTheory64 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at65 : Not (AssociativeTheory65 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3255

theorem not_model54_at66 : Not (AssociativeTheory66 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at67 : Not (AssociativeTheory67 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3256

theorem not_model54_at68 : Not (AssociativeTheory68 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3258

theorem not_model54_at69 : Not (AssociativeTheory69 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at70 : Not (AssociativeTheory70 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3255

theorem not_model54_at71 : Not (AssociativeTheory71 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3259

theorem not_model54_at72 : Not (AssociativeTheory72 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3260

theorem not_model54_at73 : Not (AssociativeTheory73 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at74 : Not (AssociativeTheory74 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3261

theorem not_model54_at75 : Not (AssociativeTheory75 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3264

theorem not_model54_at76 : Not (AssociativeTheory76 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at77 : Not (AssociativeTheory77 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq308

theorem not_model54_at78 : Not (AssociativeTheory78 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq312

theorem not_model54_at79 : Not (AssociativeTheory79 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3260

theorem not_model54_at80 : Not (AssociativeTheory80 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at81 : Not (AssociativeTheory81 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3265

theorem not_model54_at82 : Not (AssociativeTheory82 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at83 : Not (AssociativeTheory83 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3260

theorem not_model54_at84 : Not (AssociativeTheory84 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at85 : Not (AssociativeTheory85 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3264

theorem not_model54_at86 : Not (AssociativeTheory86 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at87 : Not (AssociativeTheory87 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3260

theorem not_model54_at88 : Not (AssociativeTheory88 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at89 : Not (AssociativeTheory89 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at90 : Not (AssociativeTheory90 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at91 : Not (AssociativeTheory91 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at92 : Not (AssociativeTheory92 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at93 : Not (AssociativeTheory93 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at94 : Not (AssociativeTheory94 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3271

theorem not_model54_at95 : Not (AssociativeTheory95 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3274

theorem not_model54_at96 : Not (AssociativeTheory96 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3264

theorem not_model54_at97 : Not (AssociativeTheory97 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3278

theorem not_model54_at98 : Not (AssociativeTheory98 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3292

theorem not_model54_at99 : Not (AssociativeTheory99 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3264

theorem not_model54_at100 : Not (AssociativeTheory100 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3274

theorem not_model54_at101 : Not (AssociativeTheory101 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3264

theorem not_model54_at102 : Not (AssociativeTheory102 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3300

theorem not_model54_at103 : Not (AssociativeTheory103 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at104 : Not (AssociativeTheory104 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3306

theorem not_model54_at105 : Not (AssociativeTheory105 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at106 : Not (AssociativeTheory106 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at107 : Not (AssociativeTheory107 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3256

theorem not_model54_at108 : Not (AssociativeTheory108 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3261

theorem not_model54_at109 : Not (AssociativeTheory109 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3271

theorem not_model54_at110 : Not (AssociativeTheory110 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3278

theorem not_model54_at111 : Not (AssociativeTheory111 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3308

theorem not_model54_at112 : Not (AssociativeTheory112 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at113 : Not (AssociativeTheory113 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3315

theorem not_model54_at114 : Not (AssociativeTheory114 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at115 : Not (AssociativeTheory115 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3256

theorem not_model54_at116 : Not (AssociativeTheory116 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3306

theorem not_model54_at117 : Not (AssociativeTheory117 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3316

theorem not_model54_at118 : Not (AssociativeTheory118 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at119 : Not (AssociativeTheory119 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at120 : Not (AssociativeTheory120 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3319

theorem not_model54_at121 : Not (AssociativeTheory121 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3306

theorem not_model54_at122 : Not (AssociativeTheory122 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3346

theorem not_model54_at123 : Not (AssociativeTheory123 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at124 : Not (AssociativeTheory124 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3353

theorem not_model54_at125 : Not (AssociativeTheory125 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at126 : Not (AssociativeTheory126 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3319

theorem not_model54_at127 : Not (AssociativeTheory127 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at128 : Not (AssociativeTheory128 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at129 : Not (AssociativeTheory129 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at130 : Not (AssociativeTheory130 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at131 : Not (AssociativeTheory131 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at132 : Not (AssociativeTheory132 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at133 : Not (AssociativeTheory133 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at134 : Not (AssociativeTheory134 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at135 : Not (AssociativeTheory135 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at136 : Not (AssociativeTheory136 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4271

theorem not_model54_at137 : Not (AssociativeTheory137 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at138 : Not (AssociativeTheory138 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4272

theorem not_model54_at139 : Not (AssociativeTheory139 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at140 : Not (AssociativeTheory140 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at141 : Not (AssociativeTheory141 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at142 : Not (AssociativeTheory142 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at143 : Not (AssociativeTheory143 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at144 : Not (AssociativeTheory144 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4271

theorem not_model54_at145 : Not (AssociativeTheory145 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4273

theorem not_model54_at146 : Not (AssociativeTheory146 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at147 : Not (AssociativeTheory147 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at148 : Not (AssociativeTheory148 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at149 : Not (AssociativeTheory149 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at150 : Not (AssociativeTheory150 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4275

theorem not_model54_at151 : Not (AssociativeTheory151 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at152 : Not (AssociativeTheory152 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at153 : Not (AssociativeTheory153 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at154 : Not (AssociativeTheory154 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4272

theorem not_model54_at155 : Not (AssociativeTheory155 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at156 : Not (AssociativeTheory156 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4273

theorem not_model54_at157 : Not (AssociativeTheory157 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem model54_at158 : AssociativeTheory158 (Fin 27) :=
  ⟨model54_eq4276, model54_eq4512⟩

theorem not_model54_at159 : Not (AssociativeTheory159 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at160 : Not (AssociativeTheory160 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4278

theorem not_model54_at161 : Not (AssociativeTheory161 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at162 : Not (AssociativeTheory162 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at163 : Not (AssociativeTheory163 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at164 : Not (AssociativeTheory164 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at165 : Not (AssociativeTheory165 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at166 : Not (AssociativeTheory166 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq411

theorem not_model54_at167 : Not (AssociativeTheory167 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq440

theorem not_model54_at168 : Not (AssociativeTheory168 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at169 : Not (AssociativeTheory169 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3256

theorem not_model54_at170 : Not (AssociativeTheory170 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3319

theorem not_model54_at171 : Not (AssociativeTheory171 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at172 : Not (AssociativeTheory172 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4272

theorem not_model54_at173 : Not (AssociativeTheory173 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at174 : Not (AssociativeTheory174 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at175 : Not (AssociativeTheory175 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at176 : Not (AssociativeTheory176 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at177 : Not (AssociativeTheory177 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at178 : Not (AssociativeTheory178 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at179 : Not (AssociativeTheory179 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4273

theorem not_model54_at180 : Not (AssociativeTheory180 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at181 : Not (AssociativeTheory181 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq43

theorem not_model54_at182 : Not (AssociativeTheory182 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at183 : Not (AssociativeTheory183 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at184 : Not (AssociativeTheory184 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at185 : Not (AssociativeTheory185 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4287

theorem not_model54_at186 : Not (AssociativeTheory186 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at187 : Not (AssociativeTheory187 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at188 : Not (AssociativeTheory188 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at189 : Not (AssociativeTheory189 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq411

theorem not_model54_at190 : Not (AssociativeTheory190 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at191 : Not (AssociativeTheory191 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at192 : Not (AssociativeTheory192 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4273

theorem not_model54_at193 : Not (AssociativeTheory193 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at194 : Not (AssociativeTheory194 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at195 : Not (AssociativeTheory195 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at196 : Not (AssociativeTheory196 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at197 : Not (AssociativeTheory197 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at198 : Not (AssociativeTheory198 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at199 : Not (AssociativeTheory199 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at200 : Not (AssociativeTheory200 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at201 : Not (AssociativeTheory201 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at202 : Not (AssociativeTheory202 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at203 : Not (AssociativeTheory203 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at204 : Not (AssociativeTheory204 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at205 : Not (AssociativeTheory205 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at206 : Not (AssociativeTheory206 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at207 : Not (AssociativeTheory207 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq312

theorem not_model54_at208 : Not (AssociativeTheory208 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at209 : Not (AssociativeTheory209 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at210 : Not (AssociativeTheory210 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4272

theorem not_model54_at211 : Not (AssociativeTheory211 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at212 : Not (AssociativeTheory212 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at213 : Not (AssociativeTheory213 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at214 : Not (AssociativeTheory214 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at215 : Not (AssociativeTheory215 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at216 : Not (AssociativeTheory216 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at217 : Not (AssociativeTheory217 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at218 : Not (AssociativeTheory218 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at219 : Not (AssociativeTheory219 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at220 : Not (AssociativeTheory220 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at221 : Not (AssociativeTheory221 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at222 : Not (AssociativeTheory222 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at223 : Not (AssociativeTheory223 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at224 : Not (AssociativeTheory224 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at225 : Not (AssociativeTheory225 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at226 : Not (AssociativeTheory226 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at227 : Not (AssociativeTheory227 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at228 : Not (AssociativeTheory228 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4300

theorem not_model54_at229 : Not (AssociativeTheory229 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at230 : Not (AssociativeTheory230 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4314

theorem not_model54_at231 : Not (AssociativeTheory231 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at232 : Not (AssociativeTheory232 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq308

theorem not_model54_at233 : Not (AssociativeTheory233 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at234 : Not (AssociativeTheory234 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at235 : Not (AssociativeTheory235 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4275

theorem not_model54_at236 : Not (AssociativeTheory236 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4314

theorem not_model54_at237 : Not (AssociativeTheory237 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at238 : Not (AssociativeTheory238 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at239 : Not (AssociativeTheory239 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4315

theorem not_model54_at240 : Not (AssociativeTheory240 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at241 : Not (AssociativeTheory241 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4320

theorem not_model54_at242 : Not (AssociativeTheory242 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4320

theorem not_model54_at243 : Not (AssociativeTheory243 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4320

theorem not_model54_at244 : Not (AssociativeTheory244 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at245 : Not (AssociativeTheory245 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at246 : Not (AssociativeTheory246 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq411

theorem not_model54_at247 : Not (AssociativeTheory247 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq513

theorem not_model54_at248 : Not (AssociativeTheory248 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at249 : Not (AssociativeTheory249 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3261

theorem not_model54_at250 : Not (AssociativeTheory250 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3306

theorem not_model54_at251 : Not (AssociativeTheory251 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at252 : Not (AssociativeTheory252 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4275

theorem not_model54_at253 : Not (AssociativeTheory253 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4320

theorem not_model54_at254 : Not (AssociativeTheory254 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at255 : Not (AssociativeTheory255 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at256 : Not (AssociativeTheory256 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4314

theorem not_model54_at257 : Not (AssociativeTheory257 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at258 : Not (AssociativeTheory258 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at259 : Not (AssociativeTheory259 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at260 : Not (AssociativeTheory260 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4314

theorem not_model54_at261 : Not (AssociativeTheory261 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at262 : Not (AssociativeTheory262 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at263 : Not (AssociativeTheory263 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4321

theorem not_model54_at264 : Not (AssociativeTheory264 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at265 : Not (AssociativeTheory265 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at266 : Not (AssociativeTheory266 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3260

theorem not_model54_at267 : Not (AssociativeTheory267 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3265

theorem not_model54_at268 : Not (AssociativeTheory268 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3260

theorem not_model54_at269 : Not (AssociativeTheory269 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at270 : Not (AssociativeTheory270 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at271 : Not (AssociativeTheory271 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at272 : Not (AssociativeTheory272 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at273 : Not (AssociativeTheory273 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4321

theorem not_model54_at274 : Not (AssociativeTheory274 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at275 : Not (AssociativeTheory275 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at276 : Not (AssociativeTheory276 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at277 : Not (AssociativeTheory277 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at278 : Not (AssociativeTheory278 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at279 : Not (AssociativeTheory279 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at280 : Not (AssociativeTheory280 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at281 : Not (AssociativeTheory281 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at282 : Not (AssociativeTheory282 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at283 : Not (AssociativeTheory283 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at284 : Not (AssociativeTheory284 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at285 : Not (AssociativeTheory285 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4343

theorem not_model54_at286 : Not (AssociativeTheory286 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at287 : Not (AssociativeTheory287 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at288 : Not (AssociativeTheory288 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at289 : Not (AssociativeTheory289 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at290 : Not (AssociativeTheory290 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4343

theorem not_model54_at291 : Not (AssociativeTheory291 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at292 : Not (AssociativeTheory292 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at293 : Not (AssociativeTheory293 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at294 : Not (AssociativeTheory294 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at295 : Not (AssociativeTheory295 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at296 : Not (AssociativeTheory296 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at297 : Not (AssociativeTheory297 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at298 : Not (AssociativeTheory298 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at299 : Not (AssociativeTheory299 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at300 : Not (AssociativeTheory300 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4321

theorem not_model54_at301 : Not (AssociativeTheory301 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at302 : Not (AssociativeTheory302 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at303 : Not (AssociativeTheory303 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4321

theorem not_model54_at304 : Not (AssociativeTheory304 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at305 : Not (AssociativeTheory305 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at306 : Not (AssociativeTheory306 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4358

theorem not_model54_at307 : Not (AssociativeTheory307 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3

theorem not_model54_at308 : Not (AssociativeTheory308 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at309 : Not (AssociativeTheory309 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at310 : Not (AssociativeTheory310 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4358

theorem not_model54_at311 : Not (AssociativeTheory311 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at312 : Not (AssociativeTheory312 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at313 : Not (AssociativeTheory313 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq308

theorem not_model54_at314 : Not (AssociativeTheory314 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at315 : Not (AssociativeTheory315 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at316 : Not (AssociativeTheory316 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq411

theorem not_model54_at317 : Not (AssociativeTheory317 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at318 : Not (AssociativeTheory318 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3256

theorem not_model54_at319 : Not (AssociativeTheory319 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at320 : Not (AssociativeTheory320 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at321 : Not (AssociativeTheory321 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3306

theorem not_model54_at322 : Not (AssociativeTheory322 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3319

theorem not_model54_at323 : Not (AssociativeTheory323 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at324 : Not (AssociativeTheory324 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at325 : Not (AssociativeTheory325 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at326 : Not (AssociativeTheory326 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4272

theorem not_model54_at327 : Not (AssociativeTheory327 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at328 : Not (AssociativeTheory328 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4273

theorem not_model54_at329 : Not (AssociativeTheory329 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at330 : Not (AssociativeTheory330 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at331 : Not (AssociativeTheory331 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4358

theorem not_model54_at332 : Not (AssociativeTheory332 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at333 : Not (AssociativeTheory333 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at334 : Not (AssociativeTheory334 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at335 : Not (AssociativeTheory335 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at336 : Not (AssociativeTheory336 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at337 : Not (AssociativeTheory337 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at338 : Not (AssociativeTheory338 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4290

theorem not_model54_at339 : Not (AssociativeTheory339 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at340 : Not (AssociativeTheory340 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at341 : Not (AssociativeTheory341 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at342 : Not (AssociativeTheory342 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at343 : Not (AssociativeTheory343 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at344 : Not (AssociativeTheory344 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at345 : Not (AssociativeTheory345 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at346 : Not (AssociativeTheory346 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4343

theorem not_model54_at347 : Not (AssociativeTheory347 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at348 : Not (AssociativeTheory348 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4343

theorem not_model54_at349 : Not (AssociativeTheory349 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at350 : Not (AssociativeTheory350 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at351 : Not (AssociativeTheory351 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4362

theorem not_model54_at352 : Not (AssociativeTheory352 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3

theorem not_model54_at353 : Not (AssociativeTheory353 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq8

theorem not_model54_at354 : Not (AssociativeTheory354 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at355 : Not (AssociativeTheory355 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4362

theorem not_model54_at356 : Not (AssociativeTheory356 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at357 : Not (AssociativeTheory357 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at358 : Not (AssociativeTheory358 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at359 : Not (AssociativeTheory359 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq323

theorem not_model54_at360 : Not (AssociativeTheory360 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq326

theorem not_model54_at361 : Not (AssociativeTheory361 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq411

theorem not_model54_at362 : Not (AssociativeTheory362 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at363 : Not (AssociativeTheory363 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3261

theorem not_model54_at364 : Not (AssociativeTheory364 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at365 : Not (AssociativeTheory365 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3300

theorem not_model54_at366 : Not (AssociativeTheory366 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3306

theorem not_model54_at367 : Not (AssociativeTheory367 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3319

theorem not_model54_at368 : Not (AssociativeTheory368 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at369 : Not (AssociativeTheory369 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at370 : Not (AssociativeTheory370 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at371 : Not (AssociativeTheory371 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at372 : Not (AssociativeTheory372 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at373 : Not (AssociativeTheory373 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4275

theorem not_model54_at374 : Not (AssociativeTheory374 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at375 : Not (AssociativeTheory375 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at376 : Not (AssociativeTheory376 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4362

theorem not_model54_at377 : Not (AssociativeTheory377 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at378 : Not (AssociativeTheory378 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at379 : Not (AssociativeTheory379 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at380 : Not (AssociativeTheory380 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at381 : Not (AssociativeTheory381 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at382 : Not (AssociativeTheory382 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at383 : Not (AssociativeTheory383 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at384 : Not (AssociativeTheory384 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at385 : Not (AssociativeTheory385 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at386 : Not (AssociativeTheory386 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at387 : Not (AssociativeTheory387 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at388 : Not (AssociativeTheory388 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at389 : Not (AssociativeTheory389 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at390 : Not (AssociativeTheory390 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4314

theorem not_model54_at391 : Not (AssociativeTheory391 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at392 : Not (AssociativeTheory392 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at393 : Not (AssociativeTheory393 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4314

theorem not_model54_at394 : Not (AssociativeTheory394 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at395 : Not (AssociativeTheory395 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4293

theorem not_model54_at396 : Not (AssociativeTheory396 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4358

theorem not_model54_at397 : Not (AssociativeTheory397 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at398 : Not (AssociativeTheory398 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at399 : Not (AssociativeTheory399 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at400 : Not (AssociativeTheory400 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at401 : Not (AssociativeTheory401 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at402 : Not (AssociativeTheory402 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at403 : Not (AssociativeTheory403 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at404 : Not (AssociativeTheory404 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4358

theorem not_model54_at405 : Not (AssociativeTheory405 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at406 : Not (AssociativeTheory406 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at407 : Not (AssociativeTheory407 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at408 : Not (AssociativeTheory408 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4364

theorem not_model54_at409 : Not (AssociativeTheory409 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at410 : Not (AssociativeTheory410 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at411 : Not (AssociativeTheory411 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at412 : Not (AssociativeTheory412 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at413 : Not (AssociativeTheory413 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at414 : Not (AssociativeTheory414 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at415 : Not (AssociativeTheory415 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at416 : Not (AssociativeTheory416 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4364

theorem not_model54_at417 : Not (AssociativeTheory417 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at418 : Not (AssociativeTheory418 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at419 : Not (AssociativeTheory419 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at420 : Not (AssociativeTheory420 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4369

theorem not_model54_at421 : Not (AssociativeTheory421 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at422 : Not (AssociativeTheory422 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at423 : Not (AssociativeTheory423 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at424 : Not (AssociativeTheory424 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at425 : Not (AssociativeTheory425 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at426 : Not (AssociativeTheory426 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at427 : Not (AssociativeTheory427 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq309

theorem not_model54_at428 : Not (AssociativeTheory428 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at429 : Not (AssociativeTheory429 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at430 : Not (AssociativeTheory430 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at431 : Not (AssociativeTheory431 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at432 : Not (AssociativeTheory432 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4273

theorem not_model54_at433 : Not (AssociativeTheory433 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at434 : Not (AssociativeTheory434 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4270

theorem not_model54_at435 : Not (AssociativeTheory435 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4369

theorem not_model54_at436 : Not (AssociativeTheory436 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at437 : Not (AssociativeTheory437 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at438 : Not (AssociativeTheory438 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3253

theorem not_model54_at439 : Not (AssociativeTheory439 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at440 : Not (AssociativeTheory440 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at441 : Not (AssociativeTheory441 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at442 : Not (AssociativeTheory442 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4269

theorem not_model54_at443 : Not (AssociativeTheory443 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at444 : Not (AssociativeTheory444 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at445 : Not (AssociativeTheory445 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at446 : Not (AssociativeTheory446 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4283

theorem not_model54_at447 : Not (AssociativeTheory447 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at448 : Not (AssociativeTheory448 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4291

theorem not_model54_at449 : Not (AssociativeTheory449 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4321

theorem not_model54_at450 : Not (AssociativeTheory450 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq40

theorem not_model54_at451 : Not (AssociativeTheory451 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq307

theorem not_model54_at452 : Not (AssociativeTheory452 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq3267

theorem not_model54_at453 : Not (AssociativeTheory453 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4268

theorem not_model54_at454 : Not (AssociativeTheory454 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4321

theorem not_model54_at455 : Not (AssociativeTheory455 (Fin 27)) := by
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284

theorem not_model54_at456 : Not (AssociativeTheory456 (Fin 27)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model54_eq4284
