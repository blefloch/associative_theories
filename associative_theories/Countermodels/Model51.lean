import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model51_op := finOpTable "[[1,1,3,1,1,4,8,1,1,7,1,10],[1,1,1,1,1,1,1,1,1,1,1,1],[5,1,1,4,1,1,11,1,9,1,7,1],[4,1,1,1,1,1,10,1,7,1,1,1],[1,1,1,1,1,1,7,1,1,1,1,1],[1,1,4,1,1,1,9,1,1,1,1,7],[1,1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1,1]]"
private def model51 : Magma (Fin 12) where op := model51_op
private instance : Magma (Fin 12) := model51

private theorem model51_eq1 : Equation1 (Fin 12) := by decideFin!
private theorem not_model51_eq2 : Not (Equation2 (Fin 12)) := by decideFin!
private theorem not_model51_eq3 : Not (Equation3 (Fin 12)) := by decideFin!
private theorem not_model51_eq4 : Not (Equation4 (Fin 12)) := by decideFin!
private theorem not_model51_eq5 : Not (Equation5 (Fin 12)) := by decideFin!
private theorem not_model51_eq8 : Not (Equation8 (Fin 12)) := by decideFin!
private theorem not_model51_eq10 : Not (Equation10 (Fin 12)) := by decideFin!
private theorem not_model51_eq11 : Not (Equation11 (Fin 12)) := by decideFin!
private theorem not_model51_eq14 : Not (Equation14 (Fin 12)) := by decideFin!
private theorem not_model51_eq16 : Not (Equation16 (Fin 12)) := by decideFin!
private theorem not_model51_eq38 : Not (Equation38 (Fin 12)) := by decideFin!
private theorem not_model51_eq39 : Not (Equation39 (Fin 12)) := by decideFin!
private theorem model51_eq40 : Equation40 (Fin 12) := by decideFin!
private theorem not_model51_eq41 : Not (Equation41 (Fin 12)) := by decideFin!
private theorem not_model51_eq43 : Not (Equation43 (Fin 12)) := by decideFin!
private theorem not_model51_eq47 : Not (Equation47 (Fin 12)) := by decideFin!
private theorem not_model51_eq56 : Not (Equation56 (Fin 12)) := by decideFin!
private theorem not_model51_eq66 : Not (Equation66 (Fin 12)) := by decideFin!
private theorem not_model51_eq75 : Not (Equation75 (Fin 12)) := by decideFin!
private theorem model51_eq307 : Equation307 (Fin 12) := by decideFin!
private theorem model51_eq308 : Equation308 (Fin 12) := by decideFin!
private theorem not_model51_eq309 : Not (Equation309 (Fin 12)) := by decideFin!
private theorem model51_eq310 : Equation310 (Fin 12) := by decideFin!
private theorem not_model51_eq311 : Not (Equation311 (Fin 12)) := by decideFin!
private theorem model51_eq312 : Equation312 (Fin 12) := by decideFin!
private theorem not_model51_eq313 : Not (Equation313 (Fin 12)) := by decideFin!
private theorem not_model51_eq314 : Not (Equation314 (Fin 12)) := by decideFin!
private theorem model51_eq315 : Equation315 (Fin 12) := by decideFin!
private theorem model51_eq316 : Equation316 (Fin 12) := by decideFin!
private theorem not_model51_eq318 : Not (Equation318 (Fin 12)) := by decideFin!
private theorem not_model51_eq323 : Not (Equation323 (Fin 12)) := by decideFin!
private theorem not_model51_eq325 : Not (Equation325 (Fin 12)) := by decideFin!
private theorem not_model51_eq326 : Not (Equation326 (Fin 12)) := by decideFin!
private theorem not_model51_eq327 : Not (Equation327 (Fin 12)) := by decideFin!
private theorem not_model51_eq329 : Not (Equation329 (Fin 12)) := by decideFin!
private theorem not_model51_eq332 : Not (Equation332 (Fin 12)) := by decideFin!
private theorem not_model51_eq333 : Not (Equation333 (Fin 12)) := by decideFin!
private theorem not_model51_eq343 : Not (Equation343 (Fin 12)) := by decideFin!
private theorem not_model51_eq411 : Not (Equation411 (Fin 12)) := by decideFin!
private theorem not_model51_eq419 : Not (Equation419 (Fin 12)) := by decideFin!
private theorem not_model51_eq429 : Not (Equation429 (Fin 12)) := by decideFin!
private theorem not_model51_eq440 : Not (Equation440 (Fin 12)) := by decideFin!
private theorem not_model51_eq477 : Not (Equation477 (Fin 12)) := by decideFin!
private theorem not_model51_eq504 : Not (Equation504 (Fin 12)) := by decideFin!
private theorem not_model51_eq513 : Not (Equation513 (Fin 12)) := by decideFin!
private theorem model51_eq3253 : Equation3253 (Fin 12) := by decideFin!
private theorem model51_eq3255 : Equation3255 (Fin 12) := by decideFin!
private theorem model51_eq3256 : Equation3256 (Fin 12) := by decideFin!
private theorem model51_eq3258 : Equation3258 (Fin 12) := by decideFin!
private theorem model51_eq3259 : Equation3259 (Fin 12) := by decideFin!
private theorem not_model51_eq3260 : Not (Equation3260 (Fin 12)) := by decideFin!
private theorem model51_eq3261 : Equation3261 (Fin 12) := by decideFin!
private theorem model51_eq3264 : Equation3264 (Fin 12) := by decideFin!
private theorem model51_eq3265 : Equation3265 (Fin 12) := by decideFin!
private theorem not_model51_eq3267 : Not (Equation3267 (Fin 12)) := by decideFin!
private theorem model51_eq3271 : Equation3271 (Fin 12) := by decideFin!
private theorem not_model51_eq3273 : Not (Equation3273 (Fin 12)) := by decideFin!
private theorem model51_eq3274 : Equation3274 (Fin 12) := by decideFin!
private theorem model51_eq3275 : Equation3275 (Fin 12) := by decideFin!
private theorem not_model51_eq3277 : Not (Equation3277 (Fin 12)) := by decideFin!
private theorem model51_eq3278 : Equation3278 (Fin 12) := by decideFin!
private theorem model51_eq3290 : Equation3290 (Fin 12) := by decideFin!
private theorem not_model51_eq3292 : Not (Equation3292 (Fin 12)) := by decideFin!
private theorem not_model51_eq3300 : Not (Equation3300 (Fin 12)) := by decideFin!
private theorem not_model51_eq3306 : Not (Equation3306 (Fin 12)) := by decideFin!
private theorem not_model51_eq3308 : Not (Equation3308 (Fin 12)) := by decideFin!
private theorem not_model51_eq3309 : Not (Equation3309 (Fin 12)) := by decideFin!
private theorem not_model51_eq3315 : Not (Equation3315 (Fin 12)) := by decideFin!
private theorem not_model51_eq3316 : Not (Equation3316 (Fin 12)) := by decideFin!
private theorem not_model51_eq3319 : Not (Equation3319 (Fin 12)) := by decideFin!
private theorem not_model51_eq3322 : Not (Equation3322 (Fin 12)) := by decideFin!
private theorem not_model51_eq3323 : Not (Equation3323 (Fin 12)) := by decideFin!
private theorem not_model51_eq3326 : Not (Equation3326 (Fin 12)) := by decideFin!
private theorem not_model51_eq3331 : Not (Equation3331 (Fin 12)) := by decideFin!
private theorem not_model51_eq3334 : Not (Equation3334 (Fin 12)) := by decideFin!
private theorem not_model51_eq3342 : Not (Equation3342 (Fin 12)) := by decideFin!
private theorem not_model51_eq3346 : Not (Equation3346 (Fin 12)) := by decideFin!
private theorem not_model51_eq3350 : Not (Equation3350 (Fin 12)) := by decideFin!
private theorem not_model51_eq3353 : Not (Equation3353 (Fin 12)) := by decideFin!
private theorem not_model51_eq3388 : Not (Equation3388 (Fin 12)) := by decideFin!
private theorem not_model51_eq3414 : Not (Equation3414 (Fin 12)) := by decideFin!
private theorem model51_eq4268 : Equation4268 (Fin 12) := by decideFin!
private theorem not_model51_eq4269 : Not (Equation4269 (Fin 12)) := by decideFin!
private theorem model51_eq4270 : Equation4270 (Fin 12) := by decideFin!
private theorem not_model51_eq4271 : Not (Equation4271 (Fin 12)) := by decideFin!
private theorem model51_eq4272 : Equation4272 (Fin 12) := by decideFin!
private theorem not_model51_eq4273 : Not (Equation4273 (Fin 12)) := by decideFin!
private theorem not_model51_eq4274 : Not (Equation4274 (Fin 12)) := by decideFin!
private theorem model51_eq4275 : Equation4275 (Fin 12) := by decideFin!
private theorem model51_eq4276 : Equation4276 (Fin 12) := by decideFin!
private theorem model51_eq4277 : Equation4277 (Fin 12) := by decideFin!
private theorem not_model51_eq4278 : Not (Equation4278 (Fin 12)) := by decideFin!
private theorem not_model51_eq4279 : Not (Equation4279 (Fin 12)) := by decideFin!
private theorem model51_eq4280 : Equation4280 (Fin 12) := by decideFin!
private theorem not_model51_eq4283 : Not (Equation4283 (Fin 12)) := by decideFin!
private theorem model51_eq4284 : Equation4284 (Fin 12) := by decideFin!
private theorem not_model51_eq4286 : Not (Equation4286 (Fin 12)) := by decideFin!
private theorem not_model51_eq4287 : Not (Equation4287 (Fin 12)) := by decideFin!
private theorem model51_eq4288 : Equation4288 (Fin 12) := by decideFin!
private theorem model51_eq4290 : Equation4290 (Fin 12) := by decideFin!
private theorem not_model51_eq4291 : Not (Equation4291 (Fin 12)) := by decideFin!
private theorem model51_eq4293 : Equation4293 (Fin 12) := by decideFin!
private theorem not_model51_eq4296 : Not (Equation4296 (Fin 12)) := by decideFin!
private theorem model51_eq4297 : Equation4297 (Fin 12) := by decideFin!
private theorem model51_eq4299 : Equation4299 (Fin 12) := by decideFin!
private theorem not_model51_eq4300 : Not (Equation4300 (Fin 12)) := by decideFin!
private theorem not_model51_eq4301 : Not (Equation4301 (Fin 12)) := by decideFin!
private theorem model51_eq4304 : Equation4304 (Fin 12) := by decideFin!
private theorem not_model51_eq4305 : Not (Equation4305 (Fin 12)) := by decideFin!
private theorem not_model51_eq4314 : Not (Equation4314 (Fin 12)) := by decideFin!
private theorem not_model51_eq4315 : Not (Equation4315 (Fin 12)) := by decideFin!
private theorem not_model51_eq4318 : Not (Equation4318 (Fin 12)) := by decideFin!
private theorem not_model51_eq4320 : Not (Equation4320 (Fin 12)) := by decideFin!
private theorem model51_eq4321 : Equation4321 (Fin 12) := by decideFin!
private theorem not_model51_eq4325 : Not (Equation4325 (Fin 12)) := by decideFin!
private theorem not_model51_eq4327 : Not (Equation4327 (Fin 12)) := by decideFin!
private theorem not_model51_eq4331 : Not (Equation4331 (Fin 12)) := by decideFin!
private theorem model51_eq4343 : Equation4343 (Fin 12) := by decideFin!
private theorem not_model51_eq4358 : Not (Equation4358 (Fin 12)) := by decideFin!
private theorem not_model51_eq4362 : Not (Equation4362 (Fin 12)) := by decideFin!
private theorem not_model51_eq4364 : Not (Equation4364 (Fin 12)) := by decideFin!
private theorem not_model51_eq4369 : Not (Equation4369 (Fin 12)) := by decideFin!
private theorem model51_eq4512 : Equation4512 (Fin 12) := by decideFin!

theorem model51_at1 : AssociativeTheory1 (Fin 12) :=
  model51_eq4512

theorem not_model51_at2 : Not (AssociativeTheory2 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq2

theorem not_model51_at3 : Not (AssociativeTheory3 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3

theorem not_model51_at4 : Not (AssociativeTheory4 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4

theorem not_model51_at5 : Not (AssociativeTheory5 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq5

theorem not_model51_at6 : Not (AssociativeTheory6 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at7 : Not (AssociativeTheory7 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq10

theorem not_model51_at8 : Not (AssociativeTheory8 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq11

theorem not_model51_at9 : Not (AssociativeTheory9 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq14

theorem not_model51_at10 : Not (AssociativeTheory10 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq16

theorem not_model51_at11 : Not (AssociativeTheory11 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq38

theorem not_model51_at12 : Not (AssociativeTheory12 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq39

theorem not_model51_at13 : Not (AssociativeTheory13 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq38

theorem model51_at14 : AssociativeTheory14 (Fin 12) :=
  ⟨model51_eq40, model51_eq4512⟩

theorem not_model51_at15 : Not (AssociativeTheory15 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at16 : Not (AssociativeTheory16 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3

theorem not_model51_at17 : Not (AssociativeTheory17 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at18 : Not (AssociativeTheory18 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at19 : Not (AssociativeTheory19 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq47

theorem not_model51_at20 : Not (AssociativeTheory20 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at21 : Not (AssociativeTheory21 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq56

theorem not_model51_at22 : Not (AssociativeTheory22 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at23 : Not (AssociativeTheory23 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq75

theorem not_model51_at24 : Not (AssociativeTheory24 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq56

theorem model51_at25 : AssociativeTheory25 (Fin 12) :=
  ⟨model51_eq307, model51_eq4512⟩

theorem model51_at26 : AssociativeTheory26 (Fin 12) :=
  ⟨model51_eq40, model51_eq307, model51_eq4512⟩

theorem not_model51_at27 : Not (AssociativeTheory27 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at28 : Not (AssociativeTheory28 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem model51_at29 : AssociativeTheory29 (Fin 12) :=
  ⟨model51_eq308, model51_eq4512⟩

theorem not_model51_at30 : Not (AssociativeTheory30 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at31 : Not (AssociativeTheory31 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at32 : Not (AssociativeTheory32 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem model51_at33 : AssociativeTheory33 (Fin 12) :=
  ⟨model51_eq310, model51_eq4512⟩

theorem not_model51_at34 : Not (AssociativeTheory34 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq311

theorem not_model51_at35 : Not (AssociativeTheory35 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq311

theorem not_model51_at36 : Not (AssociativeTheory36 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem model51_at37 : AssociativeTheory37 (Fin 12) :=
  ⟨model51_eq312, model51_eq4512⟩

theorem not_model51_at38 : Not (AssociativeTheory38 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem model51_at39 : AssociativeTheory39 (Fin 12) :=
  ⟨model51_eq315, model51_eq4512⟩

theorem not_model51_at40 : Not (AssociativeTheory40 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq318

theorem not_model51_at41 : Not (AssociativeTheory41 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at42 : Not (AssociativeTheory42 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at43 : Not (AssociativeTheory43 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at44 : Not (AssociativeTheory44 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at45 : Not (AssociativeTheory45 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq325

theorem not_model51_at46 : Not (AssociativeTheory46 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3

theorem not_model51_at47 : Not (AssociativeTheory47 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq325

theorem not_model51_at48 : Not (AssociativeTheory48 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at49 : Not (AssociativeTheory49 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at50 : Not (AssociativeTheory50 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at51 : Not (AssociativeTheory51 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq333

theorem not_model51_at52 : Not (AssociativeTheory52 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3

theorem not_model51_at53 : Not (AssociativeTheory53 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at54 : Not (AssociativeTheory54 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq411

theorem not_model51_at55 : Not (AssociativeTheory55 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at56 : Not (AssociativeTheory56 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq419

theorem not_model51_at57 : Not (AssociativeTheory57 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq429

theorem not_model51_at58 : Not (AssociativeTheory58 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq440

theorem not_model51_at59 : Not (AssociativeTheory59 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at60 : Not (AssociativeTheory60 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq504

theorem not_model51_at61 : Not (AssociativeTheory61 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq513

theorem not_model51_at62 : Not (AssociativeTheory62 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq440

theorem model51_at63 : AssociativeTheory63 (Fin 12) :=
  ⟨model51_eq3253, model51_eq4512⟩

theorem not_model51_at64 : Not (AssociativeTheory64 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem model51_at65 : AssociativeTheory65 (Fin 12) :=
  ⟨model51_eq3255, model51_eq4512⟩

theorem not_model51_at66 : Not (AssociativeTheory66 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem model51_at67 : AssociativeTheory67 (Fin 12) :=
  ⟨model51_eq3256, model51_eq4512⟩

theorem model51_at68 : AssociativeTheory68 (Fin 12) :=
  ⟨model51_eq3258, model51_eq4512⟩

theorem not_model51_at69 : Not (AssociativeTheory69 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem model51_at70 : AssociativeTheory70 (Fin 12) :=
  ⟨model51_eq3255, model51_eq3258, model51_eq4512⟩

theorem model51_at71 : AssociativeTheory71 (Fin 12) :=
  ⟨model51_eq3259, model51_eq4512⟩

theorem not_model51_at72 : Not (AssociativeTheory72 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem not_model51_at73 : Not (AssociativeTheory73 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem model51_at74 : AssociativeTheory74 (Fin 12) :=
  ⟨model51_eq3261, model51_eq4512⟩

theorem model51_at75 : AssociativeTheory75 (Fin 12) :=
  ⟨model51_eq3264, model51_eq4512⟩

theorem model51_at76 : AssociativeTheory76 (Fin 12) :=
  ⟨model51_eq40, model51_eq3264, model51_eq4512⟩

theorem model51_at77 : AssociativeTheory77 (Fin 12) :=
  ⟨model51_eq308, model51_eq3264, model51_eq4512⟩

theorem model51_at78 : AssociativeTheory78 (Fin 12) :=
  ⟨model51_eq312, model51_eq3264, model51_eq4512⟩

theorem not_model51_at79 : Not (AssociativeTheory79 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem not_model51_at80 : Not (AssociativeTheory80 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem model51_at81 : AssociativeTheory81 (Fin 12) :=
  ⟨model51_eq3265, model51_eq4512⟩

theorem model51_at82 : AssociativeTheory82 (Fin 12) :=
  ⟨model51_eq40, model51_eq3265, model51_eq4512⟩

theorem not_model51_at83 : Not (AssociativeTheory83 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem not_model51_at84 : Not (AssociativeTheory84 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem model51_at85 : AssociativeTheory85 (Fin 12) :=
  ⟨model51_eq3264, model51_eq3265, model51_eq4512⟩

theorem model51_at86 : AssociativeTheory86 (Fin 12) :=
  ⟨model51_eq40, model51_eq3264, model51_eq3265, model51_eq4512⟩

theorem not_model51_at87 : Not (AssociativeTheory87 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem not_model51_at88 : Not (AssociativeTheory88 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem not_model51_at89 : Not (AssociativeTheory89 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at90 : Not (AssociativeTheory90 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at91 : Not (AssociativeTheory91 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at92 : Not (AssociativeTheory92 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at93 : Not (AssociativeTheory93 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem model51_at94 : AssociativeTheory94 (Fin 12) :=
  ⟨model51_eq3271, model51_eq4512⟩

theorem model51_at95 : AssociativeTheory95 (Fin 12) :=
  ⟨model51_eq3274, model51_eq4512⟩

theorem model51_at96 : AssociativeTheory96 (Fin 12) :=
  ⟨model51_eq3264, model51_eq3274, model51_eq4512⟩

theorem model51_at97 : AssociativeTheory97 (Fin 12) :=
  ⟨model51_eq3278, model51_eq4512⟩

theorem not_model51_at98 : Not (AssociativeTheory98 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3292

theorem not_model51_at99 : Not (AssociativeTheory99 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3292

theorem not_model51_at100 : Not (AssociativeTheory100 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3292

theorem not_model51_at101 : Not (AssociativeTheory101 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3292

theorem not_model51_at102 : Not (AssociativeTheory102 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3300

theorem not_model51_at103 : Not (AssociativeTheory103 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at104 : Not (AssociativeTheory104 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at105 : Not (AssociativeTheory105 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at106 : Not (AssociativeTheory106 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at107 : Not (AssociativeTheory107 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at108 : Not (AssociativeTheory108 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at109 : Not (AssociativeTheory109 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at110 : Not (AssociativeTheory110 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at111 : Not (AssociativeTheory111 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3308

theorem not_model51_at112 : Not (AssociativeTheory112 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at113 : Not (AssociativeTheory113 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3315

theorem not_model51_at114 : Not (AssociativeTheory114 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at115 : Not (AssociativeTheory115 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3315

theorem not_model51_at116 : Not (AssociativeTheory116 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at117 : Not (AssociativeTheory117 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3316

theorem not_model51_at118 : Not (AssociativeTheory118 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at119 : Not (AssociativeTheory119 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at120 : Not (AssociativeTheory120 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3319

theorem not_model51_at121 : Not (AssociativeTheory121 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at122 : Not (AssociativeTheory122 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3346

theorem not_model51_at123 : Not (AssociativeTheory123 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at124 : Not (AssociativeTheory124 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3353

theorem not_model51_at125 : Not (AssociativeTheory125 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at126 : Not (AssociativeTheory126 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3319

theorem model51_at127 : AssociativeTheory127 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4512⟩

theorem not_model51_at128 : Not (AssociativeTheory128 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at129 : Not (AssociativeTheory129 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at130 : Not (AssociativeTheory130 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at131 : AssociativeTheory131 (Fin 12) :=
  ⟨model51_eq4270, model51_eq4512⟩

theorem not_model51_at132 : Not (AssociativeTheory132 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem model51_at133 : AssociativeTheory133 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4270, model51_eq4512⟩

theorem not_model51_at134 : Not (AssociativeTheory134 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at135 : Not (AssociativeTheory135 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at136 : Not (AssociativeTheory136 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4271

theorem not_model51_at137 : Not (AssociativeTheory137 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem model51_at138 : AssociativeTheory138 (Fin 12) :=
  ⟨model51_eq4272, model51_eq4512⟩

theorem model51_at139 : AssociativeTheory139 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4272, model51_eq4512⟩

theorem not_model51_at140 : Not (AssociativeTheory140 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at141 : Not (AssociativeTheory141 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at142 : AssociativeTheory142 (Fin 12) :=
  ⟨model51_eq4270, model51_eq4272, model51_eq4512⟩

theorem not_model51_at143 : Not (AssociativeTheory143 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at144 : Not (AssociativeTheory144 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4271

theorem not_model51_at145 : Not (AssociativeTheory145 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at146 : Not (AssociativeTheory146 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at147 : Not (AssociativeTheory147 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at148 : Not (AssociativeTheory148 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at149 : Not (AssociativeTheory149 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem model51_at150 : AssociativeTheory150 (Fin 12) :=
  ⟨model51_eq4275, model51_eq4512⟩

theorem model51_at151 : AssociativeTheory151 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4275, model51_eq4512⟩

theorem not_model51_at152 : Not (AssociativeTheory152 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at153 : AssociativeTheory153 (Fin 12) :=
  ⟨model51_eq4270, model51_eq4275, model51_eq4512⟩

theorem model51_at154 : AssociativeTheory154 (Fin 12) :=
  ⟨model51_eq4272, model51_eq4275, model51_eq4512⟩

theorem not_model51_at155 : Not (AssociativeTheory155 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at156 : Not (AssociativeTheory156 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at157 : Not (AssociativeTheory157 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem model51_at158 : AssociativeTheory158 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4512⟩

theorem not_model51_at159 : Not (AssociativeTheory159 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at160 : Not (AssociativeTheory160 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4278

theorem not_model51_at161 : Not (AssociativeTheory161 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at162 : Not (AssociativeTheory162 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq47

theorem not_model51_at163 : Not (AssociativeTheory163 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq56

theorem not_model51_at164 : Not (AssociativeTheory164 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at165 : Not (AssociativeTheory165 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at166 : Not (AssociativeTheory166 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq411

theorem not_model51_at167 : Not (AssociativeTheory167 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq440

theorem not_model51_at168 : Not (AssociativeTheory168 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at169 : Not (AssociativeTheory169 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at170 : Not (AssociativeTheory170 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3319

theorem not_model51_at171 : Not (AssociativeTheory171 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at172 : Not (AssociativeTheory172 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at173 : Not (AssociativeTheory173 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem model51_at174 : AssociativeTheory174 (Fin 12) :=
  ⟨model51_eq4284, model51_eq4512⟩

theorem not_model51_at175 : Not (AssociativeTheory175 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem model51_at176 : AssociativeTheory176 (Fin 12) :=
  ⟨model51_eq307, model51_eq4284, model51_eq4512⟩

theorem not_model51_at177 : Not (AssociativeTheory177 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at178 : Not (AssociativeTheory178 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at179 : Not (AssociativeTheory179 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem model51_at180 : AssociativeTheory180 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4284, model51_eq4512⟩

theorem not_model51_at181 : Not (AssociativeTheory181 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq43

theorem not_model51_at182 : Not (AssociativeTheory182 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at183 : Not (AssociativeTheory183 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at184 : Not (AssociativeTheory184 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at185 : Not (AssociativeTheory185 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4287

theorem not_model51_at186 : Not (AssociativeTheory186 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4287

theorem model51_at187 : AssociativeTheory187 (Fin 12) :=
  ⟨model51_eq4290, model51_eq4512⟩

theorem model51_at188 : AssociativeTheory188 (Fin 12) :=
  ⟨model51_eq307, model51_eq4290, model51_eq4512⟩

theorem not_model51_at189 : Not (AssociativeTheory189 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq411

theorem model51_at190 : AssociativeTheory190 (Fin 12) :=
  ⟨model51_eq3253, model51_eq4290, model51_eq4512⟩

theorem not_model51_at191 : Not (AssociativeTheory191 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at192 : Not (AssociativeTheory192 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem model51_at193 : AssociativeTheory193 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4290, model51_eq4512⟩

theorem not_model51_at194 : Not (AssociativeTheory194 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at195 : Not (AssociativeTheory195 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at196 : Not (AssociativeTheory196 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at197 : Not (AssociativeTheory197 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem model51_at198 : AssociativeTheory198 (Fin 12) :=
  ⟨model51_eq4284, model51_eq4290, model51_eq4512⟩

theorem model51_at199 : AssociativeTheory199 (Fin 12) :=
  ⟨model51_eq307, model51_eq4284, model51_eq4290, model51_eq4512⟩

theorem not_model51_at200 : Not (AssociativeTheory200 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at201 : AssociativeTheory201 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4284, model51_eq4290, model51_eq4512⟩

theorem not_model51_at202 : Not (AssociativeTheory202 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at203 : Not (AssociativeTheory203 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at204 : Not (AssociativeTheory204 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at205 : Not (AssociativeTheory205 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at206 : Not (AssociativeTheory206 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at207 : Not (AssociativeTheory207 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at208 : Not (AssociativeTheory208 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at209 : Not (AssociativeTheory209 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at210 : Not (AssociativeTheory210 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at211 : Not (AssociativeTheory211 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at212 : Not (AssociativeTheory212 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at213 : Not (AssociativeTheory213 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at214 : Not (AssociativeTheory214 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at215 : Not (AssociativeTheory215 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at216 : Not (AssociativeTheory216 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at217 : Not (AssociativeTheory217 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at218 : Not (AssociativeTheory218 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at219 : Not (AssociativeTheory219 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at220 : Not (AssociativeTheory220 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at221 : Not (AssociativeTheory221 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem model51_at222 : AssociativeTheory222 (Fin 12) :=
  ⟨model51_eq4293, model51_eq4512⟩

theorem model51_at223 : AssociativeTheory223 (Fin 12) :=
  ⟨model51_eq307, model51_eq4293, model51_eq4512⟩

theorem not_model51_at224 : Not (AssociativeTheory224 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at225 : AssociativeTheory225 (Fin 12) :=
  ⟨model51_eq4270, model51_eq4293, model51_eq4512⟩

theorem not_model51_at226 : Not (AssociativeTheory226 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at227 : AssociativeTheory227 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4293, model51_eq4512⟩

theorem not_model51_at228 : Not (AssociativeTheory228 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4300

theorem not_model51_at229 : Not (AssociativeTheory229 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4300

theorem not_model51_at230 : Not (AssociativeTheory230 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at231 : Not (AssociativeTheory231 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at232 : Not (AssociativeTheory232 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at233 : Not (AssociativeTheory233 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at234 : Not (AssociativeTheory234 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at235 : Not (AssociativeTheory235 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at236 : Not (AssociativeTheory236 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at237 : Not (AssociativeTheory237 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at238 : Not (AssociativeTheory238 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at239 : Not (AssociativeTheory239 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4315

theorem not_model51_at240 : Not (AssociativeTheory240 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4315

theorem not_model51_at241 : Not (AssociativeTheory241 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at242 : Not (AssociativeTheory242 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq47

theorem not_model51_at243 : Not (AssociativeTheory243 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq75

theorem not_model51_at244 : Not (AssociativeTheory244 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at245 : Not (AssociativeTheory245 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at246 : Not (AssociativeTheory246 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq411

theorem not_model51_at247 : Not (AssociativeTheory247 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq513

theorem not_model51_at248 : Not (AssociativeTheory248 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at249 : Not (AssociativeTheory249 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at250 : Not (AssociativeTheory250 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at251 : Not (AssociativeTheory251 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at252 : Not (AssociativeTheory252 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at253 : Not (AssociativeTheory253 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at254 : Not (AssociativeTheory254 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at255 : Not (AssociativeTheory255 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4320

theorem not_model51_at256 : Not (AssociativeTheory256 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at257 : Not (AssociativeTheory257 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at258 : Not (AssociativeTheory258 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at259 : Not (AssociativeTheory259 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at260 : Not (AssociativeTheory260 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at261 : Not (AssociativeTheory261 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at262 : Not (AssociativeTheory262 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem model51_at263 : AssociativeTheory263 (Fin 12) :=
  ⟨model51_eq4321, model51_eq4512⟩

theorem model51_at264 : AssociativeTheory264 (Fin 12) :=
  ⟨model51_eq40, model51_eq4321, model51_eq4512⟩

theorem model51_at265 : AssociativeTheory265 (Fin 12) :=
  ⟨model51_eq307, model51_eq4321, model51_eq4512⟩

theorem not_model51_at266 : Not (AssociativeTheory266 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem model51_at267 : AssociativeTheory267 (Fin 12) :=
  ⟨model51_eq3265, model51_eq4321, model51_eq4512⟩

theorem not_model51_at268 : Not (AssociativeTheory268 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3260

theorem not_model51_at269 : Not (AssociativeTheory269 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem model51_at270 : AssociativeTheory270 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4321, model51_eq4512⟩

theorem model51_at271 : AssociativeTheory271 (Fin 12) :=
  ⟨model51_eq4270, model51_eq4321, model51_eq4512⟩

theorem model51_at272 : AssociativeTheory272 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4270, model51_eq4321, model51_eq4512⟩

theorem model51_at273 : AssociativeTheory273 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4321, model51_eq4512⟩

theorem model51_at274 : AssociativeTheory274 (Fin 12) :=
  ⟨model51_eq4284, model51_eq4321, model51_eq4512⟩

theorem model51_at275 : AssociativeTheory275 (Fin 12) :=
  ⟨model51_eq307, model51_eq4284, model51_eq4321, model51_eq4512⟩

theorem model51_at276 : AssociativeTheory276 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4284, model51_eq4321, model51_eq4512⟩

theorem model51_at277 : AssociativeTheory277 (Fin 12) :=
  ⟨model51_eq4290, model51_eq4321, model51_eq4512⟩

theorem model51_at278 : AssociativeTheory278 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4290, model51_eq4321, model51_eq4512⟩

theorem model51_at279 : AssociativeTheory279 (Fin 12) :=
  ⟨model51_eq4284, model51_eq4290, model51_eq4321, model51_eq4512⟩

theorem model51_at280 : AssociativeTheory280 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4284, model51_eq4290, model51_eq4321, model51_eq4512⟩

theorem model51_at281 : AssociativeTheory281 (Fin 12) :=
  ⟨model51_eq4293, model51_eq4321, model51_eq4512⟩

theorem model51_at282 : AssociativeTheory282 (Fin 12) :=
  ⟨model51_eq307, model51_eq4293, model51_eq4321, model51_eq4512⟩

theorem model51_at283 : AssociativeTheory283 (Fin 12) :=
  ⟨model51_eq4270, model51_eq4293, model51_eq4321, model51_eq4512⟩

theorem model51_at284 : AssociativeTheory284 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4293, model51_eq4321, model51_eq4512⟩

theorem model51_at285 : AssociativeTheory285 (Fin 12) :=
  ⟨model51_eq4343, model51_eq4512⟩

theorem model51_at286 : AssociativeTheory286 (Fin 12) :=
  ⟨model51_eq307, model51_eq4343, model51_eq4512⟩

theorem model51_at287 : AssociativeTheory287 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4343, model51_eq4512⟩

theorem not_model51_at288 : Not (AssociativeTheory288 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at289 : Not (AssociativeTheory289 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at290 : AssociativeTheory290 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4343, model51_eq4512⟩

theorem not_model51_at291 : Not (AssociativeTheory291 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at292 : Not (AssociativeTheory292 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at293 : Not (AssociativeTheory293 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at294 : Not (AssociativeTheory294 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at295 : Not (AssociativeTheory295 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at296 : Not (AssociativeTheory296 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem model51_at297 : AssociativeTheory297 (Fin 12) :=
  ⟨model51_eq4293, model51_eq4343, model51_eq4512⟩

theorem not_model51_at298 : Not (AssociativeTheory298 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem model51_at299 : AssociativeTheory299 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4293, model51_eq4343, model51_eq4512⟩

theorem model51_at300 : AssociativeTheory300 (Fin 12) :=
  ⟨model51_eq4321, model51_eq4343, model51_eq4512⟩

theorem model51_at301 : AssociativeTheory301 (Fin 12) :=
  ⟨model51_eq307, model51_eq4321, model51_eq4343, model51_eq4512⟩

theorem model51_at302 : AssociativeTheory302 (Fin 12) :=
  ⟨model51_eq4268, model51_eq4321, model51_eq4343, model51_eq4512⟩

theorem model51_at303 : AssociativeTheory303 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4321, model51_eq4343, model51_eq4512⟩

theorem model51_at304 : AssociativeTheory304 (Fin 12) :=
  ⟨model51_eq4293, model51_eq4321, model51_eq4343, model51_eq4512⟩

theorem model51_at305 : AssociativeTheory305 (Fin 12) :=
  ⟨model51_eq4276, model51_eq4293, model51_eq4321, model51_eq4343, model51_eq4512⟩

theorem not_model51_at306 : Not (AssociativeTheory306 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at307 : Not (AssociativeTheory307 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3

theorem not_model51_at308 : Not (AssociativeTheory308 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at309 : Not (AssociativeTheory309 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at310 : Not (AssociativeTheory310 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq47

theorem not_model51_at311 : Not (AssociativeTheory311 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at312 : Not (AssociativeTheory312 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at313 : Not (AssociativeTheory313 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at314 : Not (AssociativeTheory314 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at315 : Not (AssociativeTheory315 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at316 : Not (AssociativeTheory316 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq411

theorem not_model51_at317 : Not (AssociativeTheory317 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at318 : Not (AssociativeTheory318 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at319 : Not (AssociativeTheory319 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at320 : Not (AssociativeTheory320 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at321 : Not (AssociativeTheory321 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at322 : Not (AssociativeTheory322 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3319

theorem not_model51_at323 : Not (AssociativeTheory323 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at324 : Not (AssociativeTheory324 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at325 : Not (AssociativeTheory325 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at326 : Not (AssociativeTheory326 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at327 : Not (AssociativeTheory327 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at328 : Not (AssociativeTheory328 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at329 : Not (AssociativeTheory329 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at330 : Not (AssociativeTheory330 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at331 : Not (AssociativeTheory331 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at332 : Not (AssociativeTheory332 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at333 : Not (AssociativeTheory333 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at334 : Not (AssociativeTheory334 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at335 : Not (AssociativeTheory335 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at336 : Not (AssociativeTheory336 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at337 : Not (AssociativeTheory337 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at338 : Not (AssociativeTheory338 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at339 : Not (AssociativeTheory339 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at340 : Not (AssociativeTheory340 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at341 : Not (AssociativeTheory341 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at342 : Not (AssociativeTheory342 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at343 : Not (AssociativeTheory343 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at344 : Not (AssociativeTheory344 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at345 : Not (AssociativeTheory345 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at346 : Not (AssociativeTheory346 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at347 : Not (AssociativeTheory347 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at348 : Not (AssociativeTheory348 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at349 : Not (AssociativeTheory349 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at350 : Not (AssociativeTheory350 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at351 : Not (AssociativeTheory351 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at352 : Not (AssociativeTheory352 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3

theorem not_model51_at353 : Not (AssociativeTheory353 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq8

theorem not_model51_at354 : Not (AssociativeTheory354 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at355 : Not (AssociativeTheory355 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq47

theorem not_model51_at356 : Not (AssociativeTheory356 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at357 : Not (AssociativeTheory357 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at358 : Not (AssociativeTheory358 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at359 : Not (AssociativeTheory359 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq323

theorem not_model51_at360 : Not (AssociativeTheory360 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq326

theorem not_model51_at361 : Not (AssociativeTheory361 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq411

theorem not_model51_at362 : Not (AssociativeTheory362 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at363 : Not (AssociativeTheory363 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at364 : Not (AssociativeTheory364 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at365 : Not (AssociativeTheory365 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3300

theorem not_model51_at366 : Not (AssociativeTheory366 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3306

theorem not_model51_at367 : Not (AssociativeTheory367 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3319

theorem not_model51_at368 : Not (AssociativeTheory368 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at369 : Not (AssociativeTheory369 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at370 : Not (AssociativeTheory370 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at371 : Not (AssociativeTheory371 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at372 : Not (AssociativeTheory372 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at373 : Not (AssociativeTheory373 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at374 : Not (AssociativeTheory374 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at375 : Not (AssociativeTheory375 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at376 : Not (AssociativeTheory376 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at377 : Not (AssociativeTheory377 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at378 : Not (AssociativeTheory378 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at379 : Not (AssociativeTheory379 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at380 : Not (AssociativeTheory380 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at381 : Not (AssociativeTheory381 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at382 : Not (AssociativeTheory382 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at383 : Not (AssociativeTheory383 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at384 : Not (AssociativeTheory384 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at385 : Not (AssociativeTheory385 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at386 : Not (AssociativeTheory386 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at387 : Not (AssociativeTheory387 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at388 : Not (AssociativeTheory388 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at389 : Not (AssociativeTheory389 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4362

theorem not_model51_at390 : Not (AssociativeTheory390 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at391 : Not (AssociativeTheory391 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at392 : Not (AssociativeTheory392 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at393 : Not (AssociativeTheory393 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at394 : Not (AssociativeTheory394 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at395 : Not (AssociativeTheory395 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4314

theorem not_model51_at396 : Not (AssociativeTheory396 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at397 : Not (AssociativeTheory397 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at398 : Not (AssociativeTheory398 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at399 : Not (AssociativeTheory399 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at400 : Not (AssociativeTheory400 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at401 : Not (AssociativeTheory401 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at402 : Not (AssociativeTheory402 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at403 : Not (AssociativeTheory403 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at404 : Not (AssociativeTheory404 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at405 : Not (AssociativeTheory405 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at406 : Not (AssociativeTheory406 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at407 : Not (AssociativeTheory407 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4358

theorem not_model51_at408 : Not (AssociativeTheory408 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at409 : Not (AssociativeTheory409 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at410 : Not (AssociativeTheory410 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at411 : Not (AssociativeTheory411 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at412 : Not (AssociativeTheory412 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at413 : Not (AssociativeTheory413 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at414 : Not (AssociativeTheory414 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at415 : Not (AssociativeTheory415 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at416 : Not (AssociativeTheory416 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at417 : Not (AssociativeTheory417 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at418 : Not (AssociativeTheory418 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at419 : Not (AssociativeTheory419 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4364

theorem not_model51_at420 : Not (AssociativeTheory420 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at421 : Not (AssociativeTheory421 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at422 : Not (AssociativeTheory422 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at423 : Not (AssociativeTheory423 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at424 : Not (AssociativeTheory424 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at425 : Not (AssociativeTheory425 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at426 : Not (AssociativeTheory426 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at427 : Not (AssociativeTheory427 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq309

theorem not_model51_at428 : Not (AssociativeTheory428 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at429 : Not (AssociativeTheory429 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at430 : Not (AssociativeTheory430 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at431 : Not (AssociativeTheory431 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at432 : Not (AssociativeTheory432 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at433 : Not (AssociativeTheory433 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at434 : Not (AssociativeTheory434 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4273

theorem not_model51_at435 : Not (AssociativeTheory435 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at436 : Not (AssociativeTheory436 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at437 : Not (AssociativeTheory437 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at438 : Not (AssociativeTheory438 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at439 : Not (AssociativeTheory439 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at440 : Not (AssociativeTheory440 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at441 : Not (AssociativeTheory441 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at442 : Not (AssociativeTheory442 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4269

theorem not_model51_at443 : Not (AssociativeTheory443 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at444 : Not (AssociativeTheory444 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at445 : Not (AssociativeTheory445 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at446 : Not (AssociativeTheory446 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4283

theorem not_model51_at447 : Not (AssociativeTheory447 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at448 : Not (AssociativeTheory448 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4291

theorem not_model51_at449 : Not (AssociativeTheory449 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at450 : Not (AssociativeTheory450 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at451 : Not (AssociativeTheory451 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at452 : Not (AssociativeTheory452 (Fin 12)) := by
  refine not_and_of_not_left _ ?_
  exact not_model51_eq3267

theorem not_model51_at453 : Not (AssociativeTheory453 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at454 : Not (AssociativeTheory454 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at455 : Not (AssociativeTheory455 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369

theorem not_model51_at456 : Not (AssociativeTheory456 (Fin 12)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model51_eq4369
