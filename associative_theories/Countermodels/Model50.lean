import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model50_op := finOpTable "[[1,1,3,1,1,1,5,1,1,1,8],[1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,6,1,1,1,1,10,1],[1,1,1,1,5,1,1,1,1,8,1],[1,1,1,1,1,1,1,9,1,1,1],[1,1,1,1,1,1,1,8,1,1,1],[1,1,1,1,1,1,1,10,1,1,1],[1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1]]"
private def model50 : Magma (Fin 11) where op := model50_op
private instance : Magma (Fin 11) := model50

private theorem model50_eq1 : Equation1 (Fin 11) := by decideFin!
private theorem not_model50_eq2 : Not (Equation2 (Fin 11)) := by decideFin!
private theorem not_model50_eq3 : Not (Equation3 (Fin 11)) := by decideFin!
private theorem not_model50_eq4 : Not (Equation4 (Fin 11)) := by decideFin!
private theorem not_model50_eq5 : Not (Equation5 (Fin 11)) := by decideFin!
private theorem not_model50_eq8 : Not (Equation8 (Fin 11)) := by decideFin!
private theorem not_model50_eq10 : Not (Equation10 (Fin 11)) := by decideFin!
private theorem not_model50_eq11 : Not (Equation11 (Fin 11)) := by decideFin!
private theorem not_model50_eq14 : Not (Equation14 (Fin 11)) := by decideFin!
private theorem not_model50_eq16 : Not (Equation16 (Fin 11)) := by decideFin!
private theorem not_model50_eq38 : Not (Equation38 (Fin 11)) := by decideFin!
private theorem not_model50_eq39 : Not (Equation39 (Fin 11)) := by decideFin!
private theorem model50_eq40 : Equation40 (Fin 11) := by decideFin!
private theorem not_model50_eq41 : Not (Equation41 (Fin 11)) := by decideFin!
private theorem not_model50_eq43 : Not (Equation43 (Fin 11)) := by decideFin!
private theorem not_model50_eq47 : Not (Equation47 (Fin 11)) := by decideFin!
private theorem not_model50_eq56 : Not (Equation56 (Fin 11)) := by decideFin!
private theorem not_model50_eq66 : Not (Equation66 (Fin 11)) := by decideFin!
private theorem not_model50_eq75 : Not (Equation75 (Fin 11)) := by decideFin!
private theorem model50_eq307 : Equation307 (Fin 11) := by decideFin!
private theorem model50_eq308 : Equation308 (Fin 11) := by decideFin!
private theorem model50_eq309 : Equation309 (Fin 11) := by decideFin!
private theorem model50_eq310 : Equation310 (Fin 11) := by decideFin!
private theorem not_model50_eq311 : Not (Equation311 (Fin 11)) := by decideFin!
private theorem model50_eq312 : Equation312 (Fin 11) := by decideFin!
private theorem model50_eq313 : Equation313 (Fin 11) := by decideFin!
private theorem not_model50_eq314 : Not (Equation314 (Fin 11)) := by decideFin!
private theorem model50_eq315 : Equation315 (Fin 11) := by decideFin!
private theorem model50_eq316 : Equation316 (Fin 11) := by decideFin!
private theorem not_model50_eq318 : Not (Equation318 (Fin 11)) := by decideFin!
private theorem not_model50_eq323 : Not (Equation323 (Fin 11)) := by decideFin!
private theorem not_model50_eq325 : Not (Equation325 (Fin 11)) := by decideFin!
private theorem not_model50_eq326 : Not (Equation326 (Fin 11)) := by decideFin!
private theorem not_model50_eq327 : Not (Equation327 (Fin 11)) := by decideFin!
private theorem not_model50_eq329 : Not (Equation329 (Fin 11)) := by decideFin!
private theorem not_model50_eq332 : Not (Equation332 (Fin 11)) := by decideFin!
private theorem not_model50_eq333 : Not (Equation333 (Fin 11)) := by decideFin!
private theorem not_model50_eq343 : Not (Equation343 (Fin 11)) := by decideFin!
private theorem not_model50_eq411 : Not (Equation411 (Fin 11)) := by decideFin!
private theorem not_model50_eq419 : Not (Equation419 (Fin 11)) := by decideFin!
private theorem not_model50_eq429 : Not (Equation429 (Fin 11)) := by decideFin!
private theorem not_model50_eq440 : Not (Equation440 (Fin 11)) := by decideFin!
private theorem not_model50_eq477 : Not (Equation477 (Fin 11)) := by decideFin!
private theorem not_model50_eq504 : Not (Equation504 (Fin 11)) := by decideFin!
private theorem not_model50_eq513 : Not (Equation513 (Fin 11)) := by decideFin!
private theorem model50_eq3253 : Equation3253 (Fin 11) := by decideFin!
private theorem model50_eq3255 : Equation3255 (Fin 11) := by decideFin!
private theorem model50_eq3256 : Equation3256 (Fin 11) := by decideFin!
private theorem model50_eq3258 : Equation3258 (Fin 11) := by decideFin!
private theorem model50_eq3259 : Equation3259 (Fin 11) := by decideFin!
private theorem model50_eq3260 : Equation3260 (Fin 11) := by decideFin!
private theorem model50_eq3261 : Equation3261 (Fin 11) := by decideFin!
private theorem model50_eq3264 : Equation3264 (Fin 11) := by decideFin!
private theorem model50_eq3265 : Equation3265 (Fin 11) := by decideFin!
private theorem not_model50_eq3267 : Not (Equation3267 (Fin 11)) := by decideFin!
private theorem model50_eq3271 : Equation3271 (Fin 11) := by decideFin!
private theorem model50_eq3273 : Equation3273 (Fin 11) := by decideFin!
private theorem model50_eq3274 : Equation3274 (Fin 11) := by decideFin!
private theorem model50_eq3275 : Equation3275 (Fin 11) := by decideFin!
private theorem not_model50_eq3277 : Not (Equation3277 (Fin 11)) := by decideFin!
private theorem model50_eq3278 : Equation3278 (Fin 11) := by decideFin!
private theorem model50_eq3290 : Equation3290 (Fin 11) := by decideFin!
private theorem model50_eq3292 : Equation3292 (Fin 11) := by decideFin!
private theorem not_model50_eq3300 : Not (Equation3300 (Fin 11)) := by decideFin!
private theorem not_model50_eq3306 : Not (Equation3306 (Fin 11)) := by decideFin!
private theorem not_model50_eq3308 : Not (Equation3308 (Fin 11)) := by decideFin!
private theorem not_model50_eq3309 : Not (Equation3309 (Fin 11)) := by decideFin!
private theorem not_model50_eq3315 : Not (Equation3315 (Fin 11)) := by decideFin!
private theorem not_model50_eq3316 : Not (Equation3316 (Fin 11)) := by decideFin!
private theorem not_model50_eq3319 : Not (Equation3319 (Fin 11)) := by decideFin!
private theorem not_model50_eq3322 : Not (Equation3322 (Fin 11)) := by decideFin!
private theorem not_model50_eq3323 : Not (Equation3323 (Fin 11)) := by decideFin!
private theorem not_model50_eq3326 : Not (Equation3326 (Fin 11)) := by decideFin!
private theorem not_model50_eq3331 : Not (Equation3331 (Fin 11)) := by decideFin!
private theorem not_model50_eq3334 : Not (Equation3334 (Fin 11)) := by decideFin!
private theorem not_model50_eq3342 : Not (Equation3342 (Fin 11)) := by decideFin!
private theorem not_model50_eq3346 : Not (Equation3346 (Fin 11)) := by decideFin!
private theorem not_model50_eq3350 : Not (Equation3350 (Fin 11)) := by decideFin!
private theorem not_model50_eq3353 : Not (Equation3353 (Fin 11)) := by decideFin!
private theorem not_model50_eq3388 : Not (Equation3388 (Fin 11)) := by decideFin!
private theorem not_model50_eq3414 : Not (Equation3414 (Fin 11)) := by decideFin!
private theorem model50_eq4268 : Equation4268 (Fin 11) := by decideFin!
private theorem model50_eq4269 : Equation4269 (Fin 11) := by decideFin!
private theorem model50_eq4270 : Equation4270 (Fin 11) := by decideFin!
private theorem not_model50_eq4271 : Not (Equation4271 (Fin 11)) := by decideFin!
private theorem model50_eq4272 : Equation4272 (Fin 11) := by decideFin!
private theorem model50_eq4273 : Equation4273 (Fin 11) := by decideFin!
private theorem not_model50_eq4274 : Not (Equation4274 (Fin 11)) := by decideFin!
private theorem model50_eq4275 : Equation4275 (Fin 11) := by decideFin!
private theorem model50_eq4276 : Equation4276 (Fin 11) := by decideFin!
private theorem model50_eq4277 : Equation4277 (Fin 11) := by decideFin!
private theorem not_model50_eq4278 : Not (Equation4278 (Fin 11)) := by decideFin!
private theorem model50_eq4279 : Equation4279 (Fin 11) := by decideFin!
private theorem model50_eq4280 : Equation4280 (Fin 11) := by decideFin!
private theorem model50_eq4283 : Equation4283 (Fin 11) := by decideFin!
private theorem model50_eq4284 : Equation4284 (Fin 11) := by decideFin!
private theorem model50_eq4286 : Equation4286 (Fin 11) := by decideFin!
private theorem not_model50_eq4287 : Not (Equation4287 (Fin 11)) := by decideFin!
private theorem model50_eq4288 : Equation4288 (Fin 11) := by decideFin!
private theorem model50_eq4290 : Equation4290 (Fin 11) := by decideFin!
private theorem model50_eq4291 : Equation4291 (Fin 11) := by decideFin!
private theorem model50_eq4293 : Equation4293 (Fin 11) := by decideFin!
private theorem model50_eq4296 : Equation4296 (Fin 11) := by decideFin!
private theorem model50_eq4297 : Equation4297 (Fin 11) := by decideFin!
private theorem model50_eq4299 : Equation4299 (Fin 11) := by decideFin!
private theorem not_model50_eq4300 : Not (Equation4300 (Fin 11)) := by decideFin!
private theorem model50_eq4301 : Equation4301 (Fin 11) := by decideFin!
private theorem model50_eq4304 : Equation4304 (Fin 11) := by decideFin!
private theorem model50_eq4305 : Equation4305 (Fin 11) := by decideFin!
private theorem model50_eq4314 : Equation4314 (Fin 11) := by decideFin!
private theorem not_model50_eq4315 : Not (Equation4315 (Fin 11)) := by decideFin!
private theorem model50_eq4318 : Equation4318 (Fin 11) := by decideFin!
private theorem model50_eq4320 : Equation4320 (Fin 11) := by decideFin!
private theorem model50_eq4321 : Equation4321 (Fin 11) := by decideFin!
private theorem model50_eq4325 : Equation4325 (Fin 11) := by decideFin!
private theorem model50_eq4327 : Equation4327 (Fin 11) := by decideFin!
private theorem model50_eq4331 : Equation4331 (Fin 11) := by decideFin!
private theorem model50_eq4343 : Equation4343 (Fin 11) := by decideFin!
private theorem not_model50_eq4358 : Not (Equation4358 (Fin 11)) := by decideFin!
private theorem not_model50_eq4362 : Not (Equation4362 (Fin 11)) := by decideFin!
private theorem not_model50_eq4364 : Not (Equation4364 (Fin 11)) := by decideFin!
private theorem not_model50_eq4369 : Not (Equation4369 (Fin 11)) := by decideFin!
private theorem model50_eq4512 : Equation4512 (Fin 11) := by decideFin!

theorem model50_at1 : AssociativeTheory1 (Fin 11) :=
  model50_eq4512

theorem not_model50_at2 : Not (AssociativeTheory2 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq2

theorem not_model50_at3 : Not (AssociativeTheory3 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3

theorem not_model50_at4 : Not (AssociativeTheory4 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4

theorem not_model50_at5 : Not (AssociativeTheory5 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq5

theorem not_model50_at6 : Not (AssociativeTheory6 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at7 : Not (AssociativeTheory7 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq10

theorem not_model50_at8 : Not (AssociativeTheory8 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq11

theorem not_model50_at9 : Not (AssociativeTheory9 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq14

theorem not_model50_at10 : Not (AssociativeTheory10 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq16

theorem not_model50_at11 : Not (AssociativeTheory11 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq38

theorem not_model50_at12 : Not (AssociativeTheory12 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq39

theorem not_model50_at13 : Not (AssociativeTheory13 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq38

theorem model50_at14 : AssociativeTheory14 (Fin 11) :=
  ⟨model50_eq40, model50_eq4512⟩

theorem not_model50_at15 : Not (AssociativeTheory15 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at16 : Not (AssociativeTheory16 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3

theorem not_model50_at17 : Not (AssociativeTheory17 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at18 : Not (AssociativeTheory18 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at19 : Not (AssociativeTheory19 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq47

theorem not_model50_at20 : Not (AssociativeTheory20 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at21 : Not (AssociativeTheory21 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq56

theorem not_model50_at22 : Not (AssociativeTheory22 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at23 : Not (AssociativeTheory23 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq75

theorem not_model50_at24 : Not (AssociativeTheory24 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq56

theorem model50_at25 : AssociativeTheory25 (Fin 11) :=
  ⟨model50_eq307, model50_eq4512⟩

theorem model50_at26 : AssociativeTheory26 (Fin 11) :=
  ⟨model50_eq40, model50_eq307, model50_eq4512⟩

theorem not_model50_at27 : Not (AssociativeTheory27 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at28 : Not (AssociativeTheory28 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at29 : AssociativeTheory29 (Fin 11) :=
  ⟨model50_eq308, model50_eq4512⟩

theorem model50_at30 : AssociativeTheory30 (Fin 11) :=
  ⟨model50_eq309, model50_eq4512⟩

theorem model50_at31 : AssociativeTheory31 (Fin 11) :=
  ⟨model50_eq40, model50_eq309, model50_eq4512⟩

theorem model50_at32 : AssociativeTheory32 (Fin 11) :=
  ⟨model50_eq308, model50_eq309, model50_eq4512⟩

theorem model50_at33 : AssociativeTheory33 (Fin 11) :=
  ⟨model50_eq310, model50_eq4512⟩

theorem not_model50_at34 : Not (AssociativeTheory34 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq311

theorem not_model50_at35 : Not (AssociativeTheory35 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq311

theorem not_model50_at36 : Not (AssociativeTheory36 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at37 : AssociativeTheory37 (Fin 11) :=
  ⟨model50_eq312, model50_eq4512⟩

theorem model50_at38 : AssociativeTheory38 (Fin 11) :=
  ⟨model50_eq309, model50_eq312, model50_eq4512⟩

theorem model50_at39 : AssociativeTheory39 (Fin 11) :=
  ⟨model50_eq315, model50_eq4512⟩

theorem not_model50_at40 : Not (AssociativeTheory40 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq318

theorem not_model50_at41 : Not (AssociativeTheory41 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at42 : Not (AssociativeTheory42 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at43 : Not (AssociativeTheory43 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at44 : Not (AssociativeTheory44 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at45 : Not (AssociativeTheory45 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq325

theorem not_model50_at46 : Not (AssociativeTheory46 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3

theorem not_model50_at47 : Not (AssociativeTheory47 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq325

theorem not_model50_at48 : Not (AssociativeTheory48 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at49 : Not (AssociativeTheory49 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem not_model50_at50 : Not (AssociativeTheory50 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at51 : Not (AssociativeTheory51 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq333

theorem not_model50_at52 : Not (AssociativeTheory52 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3

theorem not_model50_at53 : Not (AssociativeTheory53 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem not_model50_at54 : Not (AssociativeTheory54 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq411

theorem not_model50_at55 : Not (AssociativeTheory55 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at56 : Not (AssociativeTheory56 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq419

theorem not_model50_at57 : Not (AssociativeTheory57 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq429

theorem not_model50_at58 : Not (AssociativeTheory58 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq440

theorem not_model50_at59 : Not (AssociativeTheory59 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at60 : Not (AssociativeTheory60 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq504

theorem not_model50_at61 : Not (AssociativeTheory61 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq513

theorem not_model50_at62 : Not (AssociativeTheory62 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq440

theorem model50_at63 : AssociativeTheory63 (Fin 11) :=
  ⟨model50_eq3253, model50_eq4512⟩

theorem not_model50_at64 : Not (AssociativeTheory64 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at65 : AssociativeTheory65 (Fin 11) :=
  ⟨model50_eq3255, model50_eq4512⟩

theorem not_model50_at66 : Not (AssociativeTheory66 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem model50_at67 : AssociativeTheory67 (Fin 11) :=
  ⟨model50_eq3256, model50_eq4512⟩

theorem model50_at68 : AssociativeTheory68 (Fin 11) :=
  ⟨model50_eq3258, model50_eq4512⟩

theorem not_model50_at69 : Not (AssociativeTheory69 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem model50_at70 : AssociativeTheory70 (Fin 11) :=
  ⟨model50_eq3255, model50_eq3258, model50_eq4512⟩

theorem model50_at71 : AssociativeTheory71 (Fin 11) :=
  ⟨model50_eq3259, model50_eq4512⟩

theorem model50_at72 : AssociativeTheory72 (Fin 11) :=
  ⟨model50_eq3260, model50_eq4512⟩

theorem model50_at73 : AssociativeTheory73 (Fin 11) :=
  ⟨model50_eq40, model50_eq3260, model50_eq4512⟩

theorem model50_at74 : AssociativeTheory74 (Fin 11) :=
  ⟨model50_eq3261, model50_eq4512⟩

theorem model50_at75 : AssociativeTheory75 (Fin 11) :=
  ⟨model50_eq3264, model50_eq4512⟩

theorem model50_at76 : AssociativeTheory76 (Fin 11) :=
  ⟨model50_eq40, model50_eq3264, model50_eq4512⟩

theorem model50_at77 : AssociativeTheory77 (Fin 11) :=
  ⟨model50_eq308, model50_eq3264, model50_eq4512⟩

theorem model50_at78 : AssociativeTheory78 (Fin 11) :=
  ⟨model50_eq312, model50_eq3264, model50_eq4512⟩

theorem model50_at79 : AssociativeTheory79 (Fin 11) :=
  ⟨model50_eq3260, model50_eq3264, model50_eq4512⟩

theorem model50_at80 : AssociativeTheory80 (Fin 11) :=
  ⟨model50_eq40, model50_eq3260, model50_eq3264, model50_eq4512⟩

theorem model50_at81 : AssociativeTheory81 (Fin 11) :=
  ⟨model50_eq3265, model50_eq4512⟩

theorem model50_at82 : AssociativeTheory82 (Fin 11) :=
  ⟨model50_eq40, model50_eq3265, model50_eq4512⟩

theorem model50_at83 : AssociativeTheory83 (Fin 11) :=
  ⟨model50_eq3260, model50_eq3265, model50_eq4512⟩

theorem model50_at84 : AssociativeTheory84 (Fin 11) :=
  ⟨model50_eq40, model50_eq3260, model50_eq3265, model50_eq4512⟩

theorem model50_at85 : AssociativeTheory85 (Fin 11) :=
  ⟨model50_eq3264, model50_eq3265, model50_eq4512⟩

theorem model50_at86 : AssociativeTheory86 (Fin 11) :=
  ⟨model50_eq40, model50_eq3264, model50_eq3265, model50_eq4512⟩

theorem model50_at87 : AssociativeTheory87 (Fin 11) :=
  ⟨model50_eq3260, model50_eq3264, model50_eq3265, model50_eq4512⟩

theorem model50_at88 : AssociativeTheory88 (Fin 11) :=
  ⟨model50_eq40, model50_eq3260, model50_eq3264, model50_eq3265, model50_eq4512⟩

theorem not_model50_at89 : Not (AssociativeTheory89 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at90 : Not (AssociativeTheory90 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at91 : Not (AssociativeTheory91 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at92 : Not (AssociativeTheory92 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at93 : Not (AssociativeTheory93 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem model50_at94 : AssociativeTheory94 (Fin 11) :=
  ⟨model50_eq3271, model50_eq4512⟩

theorem model50_at95 : AssociativeTheory95 (Fin 11) :=
  ⟨model50_eq3274, model50_eq4512⟩

theorem model50_at96 : AssociativeTheory96 (Fin 11) :=
  ⟨model50_eq3264, model50_eq3274, model50_eq4512⟩

theorem model50_at97 : AssociativeTheory97 (Fin 11) :=
  ⟨model50_eq3278, model50_eq4512⟩

theorem model50_at98 : AssociativeTheory98 (Fin 11) :=
  ⟨model50_eq3292, model50_eq4512⟩

theorem model50_at99 : AssociativeTheory99 (Fin 11) :=
  ⟨model50_eq3264, model50_eq3292, model50_eq4512⟩

theorem model50_at100 : AssociativeTheory100 (Fin 11) :=
  ⟨model50_eq3274, model50_eq3292, model50_eq4512⟩

theorem model50_at101 : AssociativeTheory101 (Fin 11) :=
  ⟨model50_eq3264, model50_eq3274, model50_eq3292, model50_eq4512⟩

theorem not_model50_at102 : Not (AssociativeTheory102 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3300

theorem not_model50_at103 : Not (AssociativeTheory103 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3300

theorem not_model50_at104 : Not (AssociativeTheory104 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at105 : Not (AssociativeTheory105 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at106 : Not (AssociativeTheory106 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at107 : Not (AssociativeTheory107 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at108 : Not (AssociativeTheory108 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at109 : Not (AssociativeTheory109 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at110 : Not (AssociativeTheory110 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at111 : Not (AssociativeTheory111 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3308

theorem not_model50_at112 : Not (AssociativeTheory112 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at113 : Not (AssociativeTheory113 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3315

theorem not_model50_at114 : Not (AssociativeTheory114 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at115 : Not (AssociativeTheory115 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3315

theorem not_model50_at116 : Not (AssociativeTheory116 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at117 : Not (AssociativeTheory117 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3316

theorem not_model50_at118 : Not (AssociativeTheory118 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at119 : Not (AssociativeTheory119 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem not_model50_at120 : Not (AssociativeTheory120 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3319

theorem not_model50_at121 : Not (AssociativeTheory121 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at122 : Not (AssociativeTheory122 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3346

theorem not_model50_at123 : Not (AssociativeTheory123 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at124 : Not (AssociativeTheory124 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3353

theorem not_model50_at125 : Not (AssociativeTheory125 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at126 : Not (AssociativeTheory126 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3319

theorem model50_at127 : AssociativeTheory127 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4512⟩

theorem not_model50_at128 : Not (AssociativeTheory128 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at129 : AssociativeTheory129 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4512⟩

theorem model50_at130 : AssociativeTheory130 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4269, model50_eq4512⟩

theorem model50_at131 : AssociativeTheory131 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4512⟩

theorem not_model50_at132 : Not (AssociativeTheory132 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at133 : AssociativeTheory133 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4270, model50_eq4512⟩

theorem model50_at134 : AssociativeTheory134 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4270, model50_eq4512⟩

theorem model50_at135 : AssociativeTheory135 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4269, model50_eq4270, model50_eq4512⟩

theorem not_model50_at136 : Not (AssociativeTheory136 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4271

theorem not_model50_at137 : Not (AssociativeTheory137 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at138 : AssociativeTheory138 (Fin 11) :=
  ⟨model50_eq4272, model50_eq4512⟩

theorem model50_at139 : AssociativeTheory139 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4272, model50_eq4512⟩

theorem model50_at140 : AssociativeTheory140 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4272, model50_eq4512⟩

theorem model50_at141 : AssociativeTheory141 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4269, model50_eq4272, model50_eq4512⟩

theorem model50_at142 : AssociativeTheory142 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4272, model50_eq4512⟩

theorem model50_at143 : AssociativeTheory143 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4270, model50_eq4272, model50_eq4512⟩

theorem not_model50_at144 : Not (AssociativeTheory144 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4271

theorem model50_at145 : AssociativeTheory145 (Fin 11) :=
  ⟨model50_eq4273, model50_eq4512⟩

theorem model50_at146 : AssociativeTheory146 (Fin 11) :=
  ⟨model50_eq40, model50_eq4273, model50_eq4512⟩

theorem model50_at147 : AssociativeTheory147 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4273, model50_eq4512⟩

theorem model50_at148 : AssociativeTheory148 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4273, model50_eq4512⟩

theorem model50_at149 : AssociativeTheory149 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4273, model50_eq4512⟩

theorem model50_at150 : AssociativeTheory150 (Fin 11) :=
  ⟨model50_eq4275, model50_eq4512⟩

theorem model50_at151 : AssociativeTheory151 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4275, model50_eq4512⟩

theorem model50_at152 : AssociativeTheory152 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4275, model50_eq4512⟩

theorem model50_at153 : AssociativeTheory153 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4275, model50_eq4512⟩

theorem model50_at154 : AssociativeTheory154 (Fin 11) :=
  ⟨model50_eq4272, model50_eq4275, model50_eq4512⟩

theorem model50_at155 : AssociativeTheory155 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4272, model50_eq4275, model50_eq4512⟩

theorem model50_at156 : AssociativeTheory156 (Fin 11) :=
  ⟨model50_eq4273, model50_eq4275, model50_eq4512⟩

theorem model50_at157 : AssociativeTheory157 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4273, model50_eq4275, model50_eq4512⟩

theorem model50_at158 : AssociativeTheory158 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4512⟩

theorem not_model50_at159 : Not (AssociativeTheory159 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem not_model50_at160 : Not (AssociativeTheory160 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4278

theorem model50_at161 : AssociativeTheory161 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4512⟩

theorem not_model50_at162 : Not (AssociativeTheory162 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq47

theorem not_model50_at163 : Not (AssociativeTheory163 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq56

theorem model50_at164 : AssociativeTheory164 (Fin 11) :=
  ⟨model50_eq307, model50_eq4283, model50_eq4512⟩

theorem not_model50_at165 : Not (AssociativeTheory165 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem not_model50_at166 : Not (AssociativeTheory166 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq411

theorem not_model50_at167 : Not (AssociativeTheory167 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq440

theorem model50_at168 : AssociativeTheory168 (Fin 11) :=
  ⟨model50_eq3253, model50_eq4283, model50_eq4512⟩

theorem model50_at169 : AssociativeTheory169 (Fin 11) :=
  ⟨model50_eq3256, model50_eq4283, model50_eq4512⟩

theorem not_model50_at170 : Not (AssociativeTheory170 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3319

theorem model50_at171 : AssociativeTheory171 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4283, model50_eq4512⟩

theorem model50_at172 : AssociativeTheory172 (Fin 11) :=
  ⟨model50_eq4272, model50_eq4283, model50_eq4512⟩

theorem model50_at173 : AssociativeTheory173 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4512⟩

theorem model50_at174 : AssociativeTheory174 (Fin 11) :=
  ⟨model50_eq4284, model50_eq4512⟩

theorem not_model50_at175 : Not (AssociativeTheory175 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at176 : AssociativeTheory176 (Fin 11) :=
  ⟨model50_eq307, model50_eq4284, model50_eq4512⟩

theorem not_model50_at177 : Not (AssociativeTheory177 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at178 : AssociativeTheory178 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4284, model50_eq4512⟩

theorem model50_at179 : AssociativeTheory179 (Fin 11) :=
  ⟨model50_eq4273, model50_eq4284, model50_eq4512⟩

theorem model50_at180 : AssociativeTheory180 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4284, model50_eq4512⟩

theorem not_model50_at181 : Not (AssociativeTheory181 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq43

theorem model50_at182 : AssociativeTheory182 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4284, model50_eq4512⟩

theorem model50_at183 : AssociativeTheory183 (Fin 11) :=
  ⟨model50_eq307, model50_eq4283, model50_eq4284, model50_eq4512⟩

theorem model50_at184 : AssociativeTheory184 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4284, model50_eq4512⟩

theorem not_model50_at185 : Not (AssociativeTheory185 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4287

theorem not_model50_at186 : Not (AssociativeTheory186 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4287

theorem model50_at187 : AssociativeTheory187 (Fin 11) :=
  ⟨model50_eq4290, model50_eq4512⟩

theorem model50_at188 : AssociativeTheory188 (Fin 11) :=
  ⟨model50_eq307, model50_eq4290, model50_eq4512⟩

theorem not_model50_at189 : Not (AssociativeTheory189 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq411

theorem model50_at190 : AssociativeTheory190 (Fin 11) :=
  ⟨model50_eq3253, model50_eq4290, model50_eq4512⟩

theorem model50_at191 : AssociativeTheory191 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4290, model50_eq4512⟩

theorem model50_at192 : AssociativeTheory192 (Fin 11) :=
  ⟨model50_eq4273, model50_eq4290, model50_eq4512⟩

theorem model50_at193 : AssociativeTheory193 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4290, model50_eq4512⟩

theorem model50_at194 : AssociativeTheory194 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4290, model50_eq4512⟩

theorem model50_at195 : AssociativeTheory195 (Fin 11) :=
  ⟨model50_eq307, model50_eq4283, model50_eq4290, model50_eq4512⟩

theorem model50_at196 : AssociativeTheory196 (Fin 11) :=
  ⟨model50_eq3253, model50_eq4283, model50_eq4290, model50_eq4512⟩

theorem model50_at197 : AssociativeTheory197 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4290, model50_eq4512⟩

theorem model50_at198 : AssociativeTheory198 (Fin 11) :=
  ⟨model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at199 : AssociativeTheory199 (Fin 11) :=
  ⟨model50_eq307, model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at200 : AssociativeTheory200 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at201 : AssociativeTheory201 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at202 : AssociativeTheory202 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at203 : AssociativeTheory203 (Fin 11) :=
  ⟨model50_eq307, model50_eq4283, model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at204 : AssociativeTheory204 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4284, model50_eq4290, model50_eq4512⟩

theorem model50_at205 : AssociativeTheory205 (Fin 11) :=
  ⟨model50_eq4291, model50_eq4512⟩

theorem model50_at206 : AssociativeTheory206 (Fin 11) :=
  ⟨model50_eq307, model50_eq4291, model50_eq4512⟩

theorem model50_at207 : AssociativeTheory207 (Fin 11) :=
  ⟨model50_eq312, model50_eq4291, model50_eq4512⟩

theorem not_model50_at208 : Not (AssociativeTheory208 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem model50_at209 : AssociativeTheory209 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4291, model50_eq4512⟩

theorem model50_at210 : AssociativeTheory210 (Fin 11) :=
  ⟨model50_eq4272, model50_eq4291, model50_eq4512⟩

theorem model50_at211 : AssociativeTheory211 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4291, model50_eq4512⟩

theorem model50_at212 : AssociativeTheory212 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4291, model50_eq4512⟩

theorem model50_at213 : AssociativeTheory213 (Fin 11) :=
  ⟨model50_eq307, model50_eq4283, model50_eq4291, model50_eq4512⟩

theorem not_model50_at214 : Not (AssociativeTheory214 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem model50_at215 : AssociativeTheory215 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4283, model50_eq4291, model50_eq4512⟩

theorem model50_at216 : AssociativeTheory216 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4291, model50_eq4512⟩

theorem model50_at217 : AssociativeTheory217 (Fin 11) :=
  ⟨model50_eq4284, model50_eq4291, model50_eq4512⟩

theorem model50_at218 : AssociativeTheory218 (Fin 11) :=
  ⟨model50_eq307, model50_eq4284, model50_eq4291, model50_eq4512⟩

theorem model50_at219 : AssociativeTheory219 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4284, model50_eq4291, model50_eq4512⟩

theorem model50_at220 : AssociativeTheory220 (Fin 11) :=
  ⟨model50_eq4290, model50_eq4291, model50_eq4512⟩

theorem model50_at221 : AssociativeTheory221 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4290, model50_eq4291, model50_eq4512⟩

theorem model50_at222 : AssociativeTheory222 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4512⟩

theorem model50_at223 : AssociativeTheory223 (Fin 11) :=
  ⟨model50_eq307, model50_eq4293, model50_eq4512⟩

theorem model50_at224 : AssociativeTheory224 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4293, model50_eq4512⟩

theorem model50_at225 : AssociativeTheory225 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4293, model50_eq4512⟩

theorem model50_at226 : AssociativeTheory226 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4270, model50_eq4293, model50_eq4512⟩

theorem model50_at227 : AssociativeTheory227 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4512⟩

theorem not_model50_at228 : Not (AssociativeTheory228 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4300

theorem not_model50_at229 : Not (AssociativeTheory229 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4300

theorem model50_at230 : AssociativeTheory230 (Fin 11) :=
  ⟨model50_eq4314, model50_eq4512⟩

theorem model50_at231 : AssociativeTheory231 (Fin 11) :=
  ⟨model50_eq307, model50_eq4314, model50_eq4512⟩

theorem model50_at232 : AssociativeTheory232 (Fin 11) :=
  ⟨model50_eq308, model50_eq4314, model50_eq4512⟩

theorem not_model50_at233 : Not (AssociativeTheory233 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem model50_at234 : AssociativeTheory234 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4314, model50_eq4512⟩

theorem model50_at235 : AssociativeTheory235 (Fin 11) :=
  ⟨model50_eq4275, model50_eq4314, model50_eq4512⟩

theorem model50_at236 : AssociativeTheory236 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4314, model50_eq4512⟩

theorem model50_at237 : AssociativeTheory237 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4314, model50_eq4512⟩

theorem model50_at238 : AssociativeTheory238 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4314, model50_eq4512⟩

theorem not_model50_at239 : Not (AssociativeTheory239 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4315

theorem not_model50_at240 : Not (AssociativeTheory240 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4315

theorem model50_at241 : AssociativeTheory241 (Fin 11) :=
  ⟨model50_eq4320, model50_eq4512⟩

theorem not_model50_at242 : Not (AssociativeTheory242 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq47

theorem not_model50_at243 : Not (AssociativeTheory243 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq75

theorem model50_at244 : AssociativeTheory244 (Fin 11) :=
  ⟨model50_eq307, model50_eq4320, model50_eq4512⟩

theorem not_model50_at245 : Not (AssociativeTheory245 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at246 : Not (AssociativeTheory246 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq411

theorem not_model50_at247 : Not (AssociativeTheory247 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq513

theorem model50_at248 : AssociativeTheory248 (Fin 11) :=
  ⟨model50_eq3253, model50_eq4320, model50_eq4512⟩

theorem model50_at249 : AssociativeTheory249 (Fin 11) :=
  ⟨model50_eq3261, model50_eq4320, model50_eq4512⟩

theorem not_model50_at250 : Not (AssociativeTheory250 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem model50_at251 : AssociativeTheory251 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4320, model50_eq4512⟩

theorem model50_at252 : AssociativeTheory252 (Fin 11) :=
  ⟨model50_eq4275, model50_eq4320, model50_eq4512⟩

theorem model50_at253 : AssociativeTheory253 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4320, model50_eq4512⟩

theorem model50_at254 : AssociativeTheory254 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4320, model50_eq4512⟩

theorem model50_at255 : AssociativeTheory255 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4320, model50_eq4512⟩

theorem model50_at256 : AssociativeTheory256 (Fin 11) :=
  ⟨model50_eq4314, model50_eq4320, model50_eq4512⟩

theorem model50_at257 : AssociativeTheory257 (Fin 11) :=
  ⟨model50_eq307, model50_eq4314, model50_eq4320, model50_eq4512⟩

theorem not_model50_at258 : Not (AssociativeTheory258 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem model50_at259 : AssociativeTheory259 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4314, model50_eq4320, model50_eq4512⟩

theorem model50_at260 : AssociativeTheory260 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4314, model50_eq4320, model50_eq4512⟩

theorem model50_at261 : AssociativeTheory261 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4314, model50_eq4320, model50_eq4512⟩

theorem model50_at262 : AssociativeTheory262 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4314, model50_eq4320, model50_eq4512⟩

theorem model50_at263 : AssociativeTheory263 (Fin 11) :=
  ⟨model50_eq4321, model50_eq4512⟩

theorem model50_at264 : AssociativeTheory264 (Fin 11) :=
  ⟨model50_eq40, model50_eq4321, model50_eq4512⟩

theorem model50_at265 : AssociativeTheory265 (Fin 11) :=
  ⟨model50_eq307, model50_eq4321, model50_eq4512⟩

theorem model50_at266 : AssociativeTheory266 (Fin 11) :=
  ⟨model50_eq3260, model50_eq4321, model50_eq4512⟩

theorem model50_at267 : AssociativeTheory267 (Fin 11) :=
  ⟨model50_eq3265, model50_eq4321, model50_eq4512⟩

theorem model50_at268 : AssociativeTheory268 (Fin 11) :=
  ⟨model50_eq3260, model50_eq3265, model50_eq4321, model50_eq4512⟩

theorem not_model50_at269 : Not (AssociativeTheory269 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem model50_at270 : AssociativeTheory270 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4321, model50_eq4512⟩

theorem model50_at271 : AssociativeTheory271 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4321, model50_eq4512⟩

theorem model50_at272 : AssociativeTheory272 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4270, model50_eq4321, model50_eq4512⟩

theorem model50_at273 : AssociativeTheory273 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4321, model50_eq4512⟩

theorem model50_at274 : AssociativeTheory274 (Fin 11) :=
  ⟨model50_eq4284, model50_eq4321, model50_eq4512⟩

theorem model50_at275 : AssociativeTheory275 (Fin 11) :=
  ⟨model50_eq307, model50_eq4284, model50_eq4321, model50_eq4512⟩

theorem model50_at276 : AssociativeTheory276 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4284, model50_eq4321, model50_eq4512⟩

theorem model50_at277 : AssociativeTheory277 (Fin 11) :=
  ⟨model50_eq4290, model50_eq4321, model50_eq4512⟩

theorem model50_at278 : AssociativeTheory278 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4290, model50_eq4321, model50_eq4512⟩

theorem model50_at279 : AssociativeTheory279 (Fin 11) :=
  ⟨model50_eq4284, model50_eq4290, model50_eq4321, model50_eq4512⟩

theorem model50_at280 : AssociativeTheory280 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4284, model50_eq4290, model50_eq4321, model50_eq4512⟩

theorem model50_at281 : AssociativeTheory281 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4321, model50_eq4512⟩

theorem model50_at282 : AssociativeTheory282 (Fin 11) :=
  ⟨model50_eq307, model50_eq4293, model50_eq4321, model50_eq4512⟩

theorem model50_at283 : AssociativeTheory283 (Fin 11) :=
  ⟨model50_eq4270, model50_eq4293, model50_eq4321, model50_eq4512⟩

theorem model50_at284 : AssociativeTheory284 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4321, model50_eq4512⟩

theorem model50_at285 : AssociativeTheory285 (Fin 11) :=
  ⟨model50_eq4343, model50_eq4512⟩

theorem model50_at286 : AssociativeTheory286 (Fin 11) :=
  ⟨model50_eq307, model50_eq4343, model50_eq4512⟩

theorem model50_at287 : AssociativeTheory287 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4343, model50_eq4512⟩

theorem model50_at288 : AssociativeTheory288 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4343, model50_eq4512⟩

theorem model50_at289 : AssociativeTheory289 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4269, model50_eq4343, model50_eq4512⟩

theorem model50_at290 : AssociativeTheory290 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4343, model50_eq4512⟩

theorem model50_at291 : AssociativeTheory291 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4343, model50_eq4512⟩

theorem model50_at292 : AssociativeTheory292 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4343, model50_eq4512⟩

theorem model50_at293 : AssociativeTheory293 (Fin 11) :=
  ⟨model50_eq4291, model50_eq4343, model50_eq4512⟩

theorem model50_at294 : AssociativeTheory294 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4291, model50_eq4343, model50_eq4512⟩

theorem model50_at295 : AssociativeTheory295 (Fin 11) :=
  ⟨model50_eq4283, model50_eq4291, model50_eq4343, model50_eq4512⟩

theorem model50_at296 : AssociativeTheory296 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4283, model50_eq4291, model50_eq4343, model50_eq4512⟩

theorem model50_at297 : AssociativeTheory297 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4343, model50_eq4512⟩

theorem model50_at298 : AssociativeTheory298 (Fin 11) :=
  ⟨model50_eq4269, model50_eq4293, model50_eq4343, model50_eq4512⟩

theorem model50_at299 : AssociativeTheory299 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4343, model50_eq4512⟩

theorem model50_at300 : AssociativeTheory300 (Fin 11) :=
  ⟨model50_eq4321, model50_eq4343, model50_eq4512⟩

theorem model50_at301 : AssociativeTheory301 (Fin 11) :=
  ⟨model50_eq307, model50_eq4321, model50_eq4343, model50_eq4512⟩

theorem model50_at302 : AssociativeTheory302 (Fin 11) :=
  ⟨model50_eq4268, model50_eq4321, model50_eq4343, model50_eq4512⟩

theorem model50_at303 : AssociativeTheory303 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4321, model50_eq4343, model50_eq4512⟩

theorem model50_at304 : AssociativeTheory304 (Fin 11) :=
  ⟨model50_eq4293, model50_eq4321, model50_eq4343, model50_eq4512⟩

theorem model50_at305 : AssociativeTheory305 (Fin 11) :=
  ⟨model50_eq4276, model50_eq4293, model50_eq4321, model50_eq4343, model50_eq4512⟩

theorem not_model50_at306 : Not (AssociativeTheory306 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at307 : Not (AssociativeTheory307 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3

theorem not_model50_at308 : Not (AssociativeTheory308 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at309 : Not (AssociativeTheory309 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at310 : Not (AssociativeTheory310 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq47

theorem not_model50_at311 : Not (AssociativeTheory311 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at312 : Not (AssociativeTheory312 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at313 : Not (AssociativeTheory313 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at314 : Not (AssociativeTheory314 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at315 : Not (AssociativeTheory315 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem not_model50_at316 : Not (AssociativeTheory316 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq411

theorem not_model50_at317 : Not (AssociativeTheory317 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at318 : Not (AssociativeTheory318 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at319 : Not (AssociativeTheory319 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at320 : Not (AssociativeTheory320 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at321 : Not (AssociativeTheory321 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at322 : Not (AssociativeTheory322 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3319

theorem not_model50_at323 : Not (AssociativeTheory323 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at324 : Not (AssociativeTheory324 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at325 : Not (AssociativeTheory325 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at326 : Not (AssociativeTheory326 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at327 : Not (AssociativeTheory327 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at328 : Not (AssociativeTheory328 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at329 : Not (AssociativeTheory329 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at330 : Not (AssociativeTheory330 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at331 : Not (AssociativeTheory331 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at332 : Not (AssociativeTheory332 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at333 : Not (AssociativeTheory333 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at334 : Not (AssociativeTheory334 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at335 : Not (AssociativeTheory335 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at336 : Not (AssociativeTheory336 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at337 : Not (AssociativeTheory337 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at338 : Not (AssociativeTheory338 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at339 : Not (AssociativeTheory339 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at340 : Not (AssociativeTheory340 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at341 : Not (AssociativeTheory341 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at342 : Not (AssociativeTheory342 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at343 : Not (AssociativeTheory343 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at344 : Not (AssociativeTheory344 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at345 : Not (AssociativeTheory345 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at346 : Not (AssociativeTheory346 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at347 : Not (AssociativeTheory347 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at348 : Not (AssociativeTheory348 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at349 : Not (AssociativeTheory349 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at350 : Not (AssociativeTheory350 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at351 : Not (AssociativeTheory351 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at352 : Not (AssociativeTheory352 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3

theorem not_model50_at353 : Not (AssociativeTheory353 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq8

theorem not_model50_at354 : Not (AssociativeTheory354 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at355 : Not (AssociativeTheory355 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq47

theorem not_model50_at356 : Not (AssociativeTheory356 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at357 : Not (AssociativeTheory357 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at358 : Not (AssociativeTheory358 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at359 : Not (AssociativeTheory359 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq323

theorem not_model50_at360 : Not (AssociativeTheory360 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq326

theorem not_model50_at361 : Not (AssociativeTheory361 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq411

theorem not_model50_at362 : Not (AssociativeTheory362 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at363 : Not (AssociativeTheory363 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at364 : Not (AssociativeTheory364 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at365 : Not (AssociativeTheory365 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3300

theorem not_model50_at366 : Not (AssociativeTheory366 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3306

theorem not_model50_at367 : Not (AssociativeTheory367 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3319

theorem not_model50_at368 : Not (AssociativeTheory368 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at369 : Not (AssociativeTheory369 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at370 : Not (AssociativeTheory370 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at371 : Not (AssociativeTheory371 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at372 : Not (AssociativeTheory372 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at373 : Not (AssociativeTheory373 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at374 : Not (AssociativeTheory374 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at375 : Not (AssociativeTheory375 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at376 : Not (AssociativeTheory376 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at377 : Not (AssociativeTheory377 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at378 : Not (AssociativeTheory378 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at379 : Not (AssociativeTheory379 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at380 : Not (AssociativeTheory380 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at381 : Not (AssociativeTheory381 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at382 : Not (AssociativeTheory382 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at383 : Not (AssociativeTheory383 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at384 : Not (AssociativeTheory384 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at385 : Not (AssociativeTheory385 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at386 : Not (AssociativeTheory386 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at387 : Not (AssociativeTheory387 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at388 : Not (AssociativeTheory388 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at389 : Not (AssociativeTheory389 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at390 : Not (AssociativeTheory390 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at391 : Not (AssociativeTheory391 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at392 : Not (AssociativeTheory392 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at393 : Not (AssociativeTheory393 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at394 : Not (AssociativeTheory394 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at395 : Not (AssociativeTheory395 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4362

theorem not_model50_at396 : Not (AssociativeTheory396 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at397 : Not (AssociativeTheory397 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at398 : Not (AssociativeTheory398 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at399 : Not (AssociativeTheory399 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at400 : Not (AssociativeTheory400 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at401 : Not (AssociativeTheory401 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at402 : Not (AssociativeTheory402 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at403 : Not (AssociativeTheory403 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at404 : Not (AssociativeTheory404 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at405 : Not (AssociativeTheory405 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at406 : Not (AssociativeTheory406 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at407 : Not (AssociativeTheory407 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4358

theorem not_model50_at408 : Not (AssociativeTheory408 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at409 : Not (AssociativeTheory409 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at410 : Not (AssociativeTheory410 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at411 : Not (AssociativeTheory411 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at412 : Not (AssociativeTheory412 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at413 : Not (AssociativeTheory413 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at414 : Not (AssociativeTheory414 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at415 : Not (AssociativeTheory415 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at416 : Not (AssociativeTheory416 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at417 : Not (AssociativeTheory417 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at418 : Not (AssociativeTheory418 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at419 : Not (AssociativeTheory419 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4364

theorem not_model50_at420 : Not (AssociativeTheory420 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at421 : Not (AssociativeTheory421 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at422 : Not (AssociativeTheory422 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at423 : Not (AssociativeTheory423 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at424 : Not (AssociativeTheory424 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at425 : Not (AssociativeTheory425 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at426 : Not (AssociativeTheory426 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at427 : Not (AssociativeTheory427 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at428 : Not (AssociativeTheory428 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at429 : Not (AssociativeTheory429 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at430 : Not (AssociativeTheory430 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at431 : Not (AssociativeTheory431 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at432 : Not (AssociativeTheory432 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at433 : Not (AssociativeTheory433 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at434 : Not (AssociativeTheory434 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at435 : Not (AssociativeTheory435 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at436 : Not (AssociativeTheory436 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at437 : Not (AssociativeTheory437 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at438 : Not (AssociativeTheory438 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at439 : Not (AssociativeTheory439 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at440 : Not (AssociativeTheory440 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at441 : Not (AssociativeTheory441 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at442 : Not (AssociativeTheory442 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at443 : Not (AssociativeTheory443 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at444 : Not (AssociativeTheory444 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at445 : Not (AssociativeTheory445 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at446 : Not (AssociativeTheory446 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at447 : Not (AssociativeTheory447 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at448 : Not (AssociativeTheory448 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at449 : Not (AssociativeTheory449 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at450 : Not (AssociativeTheory450 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at451 : Not (AssociativeTheory451 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at452 : Not (AssociativeTheory452 (Fin 11)) := by
  refine not_and_of_not_left _ ?_
  exact not_model50_eq3267

theorem not_model50_at453 : Not (AssociativeTheory453 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at454 : Not (AssociativeTheory454 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at455 : Not (AssociativeTheory455 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369

theorem not_model50_at456 : Not (AssociativeTheory456 (Fin 11)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model50_eq4369
