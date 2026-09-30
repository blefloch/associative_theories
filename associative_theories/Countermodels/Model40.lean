import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model40_op := finOpTable "[[0,0,0,0,0,0,0,0],[0,0,0,0,7,0,5,0],[0,3,0,0,0,0,0,5],[0,0,0,0,5,0,0,0],[0,0,6,5,0,0,0,0],[0,0,0,0,0,0,0,0],[0,5,0,0,0,0,0,0],[0,0,5,0,0,0,0,0]]"
private def model40 : Magma (Fin 8) where op := model40_op
private instance : Magma (Fin 8) := model40

private theorem model40_eq1 : Equation1 (Fin 8) := by decideFin!
private theorem model40_eq40 : Equation40 (Fin 8) := by decideFin!
private theorem model40_eq307 : Equation307 (Fin 8) := by decideFin!
private theorem model40_eq308 : Equation308 (Fin 8) := by decideFin!
private theorem model40_eq309 : Equation309 (Fin 8) := by decideFin!
private theorem model40_eq310 : Equation310 (Fin 8) := by decideFin!
private theorem model40_eq312 : Equation312 (Fin 8) := by decideFin!
private theorem model40_eq313 : Equation313 (Fin 8) := by decideFin!
private theorem model40_eq315 : Equation315 (Fin 8) := by decideFin!
private theorem model40_eq316 : Equation316 (Fin 8) := by decideFin!
private theorem model40_eq3253 : Equation3253 (Fin 8) := by decideFin!
private theorem model40_eq3255 : Equation3255 (Fin 8) := by decideFin!
private theorem model40_eq3256 : Equation3256 (Fin 8) := by decideFin!
private theorem model40_eq3258 : Equation3258 (Fin 8) := by decideFin!
private theorem model40_eq3259 : Equation3259 (Fin 8) := by decideFin!
private theorem model40_eq3260 : Equation3260 (Fin 8) := by decideFin!
private theorem model40_eq3261 : Equation3261 (Fin 8) := by decideFin!
private theorem model40_eq3264 : Equation3264 (Fin 8) := by decideFin!
private theorem model40_eq3265 : Equation3265 (Fin 8) := by decideFin!
private theorem model40_eq3267 : Equation3267 (Fin 8) := by decideFin!
private theorem model40_eq3271 : Equation3271 (Fin 8) := by decideFin!
private theorem model40_eq3273 : Equation3273 (Fin 8) := by decideFin!
private theorem model40_eq3274 : Equation3274 (Fin 8) := by decideFin!
private theorem model40_eq3275 : Equation3275 (Fin 8) := by decideFin!
private theorem model40_eq3277 : Equation3277 (Fin 8) := by decideFin!
private theorem model40_eq3278 : Equation3278 (Fin 8) := by decideFin!
private theorem model40_eq3290 : Equation3290 (Fin 8) := by decideFin!
private theorem model40_eq3292 : Equation3292 (Fin 8) := by decideFin!
private theorem model40_eq3300 : Equation3300 (Fin 8) := by decideFin!
private theorem model40_eq4268 : Equation4268 (Fin 8) := by decideFin!
private theorem model40_eq4269 : Equation4269 (Fin 8) := by decideFin!
private theorem model40_eq4270 : Equation4270 (Fin 8) := by decideFin!
private theorem model40_eq4272 : Equation4272 (Fin 8) := by decideFin!
private theorem model40_eq4273 : Equation4273 (Fin 8) := by decideFin!
private theorem model40_eq4275 : Equation4275 (Fin 8) := by decideFin!
private theorem model40_eq4276 : Equation4276 (Fin 8) := by decideFin!
private theorem model40_eq4277 : Equation4277 (Fin 8) := by decideFin!
private theorem model40_eq4279 : Equation4279 (Fin 8) := by decideFin!
private theorem model40_eq4280 : Equation4280 (Fin 8) := by decideFin!
private theorem model40_eq4283 : Equation4283 (Fin 8) := by decideFin!
private theorem model40_eq4284 : Equation4284 (Fin 8) := by decideFin!
private theorem model40_eq4286 : Equation4286 (Fin 8) := by decideFin!
private theorem model40_eq4288 : Equation4288 (Fin 8) := by decideFin!
private theorem model40_eq4290 : Equation4290 (Fin 8) := by decideFin!
private theorem model40_eq4291 : Equation4291 (Fin 8) := by decideFin!
private theorem model40_eq4293 : Equation4293 (Fin 8) := by decideFin!
private theorem model40_eq4296 : Equation4296 (Fin 8) := by decideFin!
private theorem model40_eq4297 : Equation4297 (Fin 8) := by decideFin!
private theorem model40_eq4299 : Equation4299 (Fin 8) := by decideFin!
private theorem model40_eq4301 : Equation4301 (Fin 8) := by decideFin!
private theorem model40_eq4304 : Equation4304 (Fin 8) := by decideFin!
private theorem model40_eq4305 : Equation4305 (Fin 8) := by decideFin!
private theorem model40_eq4314 : Equation4314 (Fin 8) := by decideFin!
private theorem model40_eq4318 : Equation4318 (Fin 8) := by decideFin!
private theorem model40_eq4320 : Equation4320 (Fin 8) := by decideFin!
private theorem model40_eq4321 : Equation4321 (Fin 8) := by decideFin!
private theorem model40_eq4325 : Equation4325 (Fin 8) := by decideFin!
private theorem model40_eq4327 : Equation4327 (Fin 8) := by decideFin!
private theorem model40_eq4331 : Equation4331 (Fin 8) := by decideFin!
private theorem model40_eq4343 : Equation4343 (Fin 8) := by decideFin!
private theorem model40_eq4364 : Equation4364 (Fin 8) := by decideFin!
private theorem model40_eq4512 : Equation4512 (Fin 8) := by decideFin!
private theorem not_model40_eq2 : Not (Equation2 (Fin 8)) := by decideFin!
private theorem not_model40_eq3 : Not (Equation3 (Fin 8)) := by decideFin!
private theorem not_model40_eq4 : Not (Equation4 (Fin 8)) := by decideFin!
private theorem not_model40_eq5 : Not (Equation5 (Fin 8)) := by decideFin!
private theorem not_model40_eq8 : Not (Equation8 (Fin 8)) := by decideFin!
private theorem not_model40_eq10 : Not (Equation10 (Fin 8)) := by decideFin!
private theorem not_model40_eq11 : Not (Equation11 (Fin 8)) := by decideFin!
private theorem not_model40_eq14 : Not (Equation14 (Fin 8)) := by decideFin!
private theorem not_model40_eq16 : Not (Equation16 (Fin 8)) := by decideFin!
private theorem not_model40_eq38 : Not (Equation38 (Fin 8)) := by decideFin!
private theorem not_model40_eq39 : Not (Equation39 (Fin 8)) := by decideFin!
private theorem not_model40_eq41 : Not (Equation41 (Fin 8)) := by decideFin!
private theorem not_model40_eq43 : Not (Equation43 (Fin 8)) := by decideFin!
private theorem not_model40_eq47 : Not (Equation47 (Fin 8)) := by decideFin!
private theorem not_model40_eq56 : Not (Equation56 (Fin 8)) := by decideFin!
private theorem not_model40_eq66 : Not (Equation66 (Fin 8)) := by decideFin!
private theorem not_model40_eq75 : Not (Equation75 (Fin 8)) := by decideFin!
private theorem not_model40_eq311 : Not (Equation311 (Fin 8)) := by decideFin!
private theorem not_model40_eq314 : Not (Equation314 (Fin 8)) := by decideFin!
private theorem not_model40_eq318 : Not (Equation318 (Fin 8)) := by decideFin!
private theorem not_model40_eq323 : Not (Equation323 (Fin 8)) := by decideFin!
private theorem not_model40_eq325 : Not (Equation325 (Fin 8)) := by decideFin!
private theorem not_model40_eq326 : Not (Equation326 (Fin 8)) := by decideFin!
private theorem not_model40_eq327 : Not (Equation327 (Fin 8)) := by decideFin!
private theorem not_model40_eq329 : Not (Equation329 (Fin 8)) := by decideFin!
private theorem not_model40_eq332 : Not (Equation332 (Fin 8)) := by decideFin!
private theorem not_model40_eq333 : Not (Equation333 (Fin 8)) := by decideFin!
private theorem not_model40_eq343 : Not (Equation343 (Fin 8)) := by decideFin!
private theorem not_model40_eq411 : Not (Equation411 (Fin 8)) := by decideFin!
private theorem not_model40_eq419 : Not (Equation419 (Fin 8)) := by decideFin!
private theorem not_model40_eq429 : Not (Equation429 (Fin 8)) := by decideFin!
private theorem not_model40_eq440 : Not (Equation440 (Fin 8)) := by decideFin!
private theorem not_model40_eq477 : Not (Equation477 (Fin 8)) := by decideFin!
private theorem not_model40_eq504 : Not (Equation504 (Fin 8)) := by decideFin!
private theorem not_model40_eq513 : Not (Equation513 (Fin 8)) := by decideFin!
private theorem not_model40_eq3306 : Not (Equation3306 (Fin 8)) := by decideFin!
private theorem not_model40_eq3308 : Not (Equation3308 (Fin 8)) := by decideFin!
private theorem not_model40_eq3309 : Not (Equation3309 (Fin 8)) := by decideFin!
private theorem not_model40_eq3315 : Not (Equation3315 (Fin 8)) := by decideFin!
private theorem not_model40_eq3316 : Not (Equation3316 (Fin 8)) := by decideFin!
private theorem not_model40_eq3319 : Not (Equation3319 (Fin 8)) := by decideFin!
private theorem not_model40_eq3322 : Not (Equation3322 (Fin 8)) := by decideFin!
private theorem not_model40_eq3323 : Not (Equation3323 (Fin 8)) := by decideFin!
private theorem not_model40_eq3326 : Not (Equation3326 (Fin 8)) := by decideFin!
private theorem not_model40_eq3331 : Not (Equation3331 (Fin 8)) := by decideFin!
private theorem not_model40_eq3334 : Not (Equation3334 (Fin 8)) := by decideFin!
private theorem not_model40_eq3342 : Not (Equation3342 (Fin 8)) := by decideFin!
private theorem not_model40_eq3346 : Not (Equation3346 (Fin 8)) := by decideFin!
private theorem not_model40_eq3350 : Not (Equation3350 (Fin 8)) := by decideFin!
private theorem not_model40_eq3353 : Not (Equation3353 (Fin 8)) := by decideFin!
private theorem not_model40_eq3388 : Not (Equation3388 (Fin 8)) := by decideFin!
private theorem not_model40_eq3414 : Not (Equation3414 (Fin 8)) := by decideFin!
private theorem not_model40_eq4271 : Not (Equation4271 (Fin 8)) := by decideFin!
private theorem not_model40_eq4274 : Not (Equation4274 (Fin 8)) := by decideFin!
private theorem not_model40_eq4278 : Not (Equation4278 (Fin 8)) := by decideFin!
private theorem not_model40_eq4287 : Not (Equation4287 (Fin 8)) := by decideFin!
private theorem not_model40_eq4300 : Not (Equation4300 (Fin 8)) := by decideFin!
private theorem not_model40_eq4315 : Not (Equation4315 (Fin 8)) := by decideFin!
private theorem not_model40_eq4358 : Not (Equation4358 (Fin 8)) := by decideFin!
private theorem not_model40_eq4362 : Not (Equation4362 (Fin 8)) := by decideFin!
private theorem not_model40_eq4369 : Not (Equation4369 (Fin 8)) := by decideFin!

theorem model40_at1 : AssociativeTheory1 (Fin 8) :=
  model40_eq4512

theorem not_model40_at2 : Not (AssociativeTheory2 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq2

theorem not_model40_at3 : Not (AssociativeTheory3 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3

theorem not_model40_at4 : Not (AssociativeTheory4 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4

theorem not_model40_at5 : Not (AssociativeTheory5 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq5

theorem not_model40_at6 : Not (AssociativeTheory6 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at7 : Not (AssociativeTheory7 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq10

theorem not_model40_at8 : Not (AssociativeTheory8 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq11

theorem not_model40_at9 : Not (AssociativeTheory9 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq14

theorem not_model40_at10 : Not (AssociativeTheory10 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq16

theorem not_model40_at11 : Not (AssociativeTheory11 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq38

theorem not_model40_at12 : Not (AssociativeTheory12 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq39

theorem not_model40_at13 : Not (AssociativeTheory13 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq38

theorem model40_at14 : AssociativeTheory14 (Fin 8) :=
  ⟨model40_eq40, model40_eq4512⟩

theorem not_model40_at15 : Not (AssociativeTheory15 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at16 : Not (AssociativeTheory16 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3

theorem not_model40_at17 : Not (AssociativeTheory17 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at18 : Not (AssociativeTheory18 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at19 : Not (AssociativeTheory19 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq47

theorem not_model40_at20 : Not (AssociativeTheory20 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at21 : Not (AssociativeTheory21 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq56

theorem not_model40_at22 : Not (AssociativeTheory22 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at23 : Not (AssociativeTheory23 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq75

theorem not_model40_at24 : Not (AssociativeTheory24 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq56

theorem model40_at25 : AssociativeTheory25 (Fin 8) :=
  ⟨model40_eq307, model40_eq4512⟩

theorem model40_at26 : AssociativeTheory26 (Fin 8) :=
  ⟨model40_eq40, model40_eq307, model40_eq4512⟩

theorem not_model40_at27 : Not (AssociativeTheory27 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at28 : Not (AssociativeTheory28 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at29 : AssociativeTheory29 (Fin 8) :=
  ⟨model40_eq308, model40_eq4512⟩

theorem model40_at30 : AssociativeTheory30 (Fin 8) :=
  ⟨model40_eq309, model40_eq4512⟩

theorem model40_at31 : AssociativeTheory31 (Fin 8) :=
  ⟨model40_eq40, model40_eq309, model40_eq4512⟩

theorem model40_at32 : AssociativeTheory32 (Fin 8) :=
  ⟨model40_eq308, model40_eq309, model40_eq4512⟩

theorem model40_at33 : AssociativeTheory33 (Fin 8) :=
  ⟨model40_eq310, model40_eq4512⟩

theorem not_model40_at34 : Not (AssociativeTheory34 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq311

theorem not_model40_at35 : Not (AssociativeTheory35 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq311

theorem not_model40_at36 : Not (AssociativeTheory36 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at37 : AssociativeTheory37 (Fin 8) :=
  ⟨model40_eq312, model40_eq4512⟩

theorem model40_at38 : AssociativeTheory38 (Fin 8) :=
  ⟨model40_eq309, model40_eq312, model40_eq4512⟩

theorem model40_at39 : AssociativeTheory39 (Fin 8) :=
  ⟨model40_eq315, model40_eq4512⟩

theorem not_model40_at40 : Not (AssociativeTheory40 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq318

theorem not_model40_at41 : Not (AssociativeTheory41 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at42 : Not (AssociativeTheory42 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at43 : Not (AssociativeTheory43 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at44 : Not (AssociativeTheory44 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at45 : Not (AssociativeTheory45 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq325

theorem not_model40_at46 : Not (AssociativeTheory46 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3

theorem not_model40_at47 : Not (AssociativeTheory47 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq325

theorem not_model40_at48 : Not (AssociativeTheory48 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at49 : Not (AssociativeTheory49 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem not_model40_at50 : Not (AssociativeTheory50 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at51 : Not (AssociativeTheory51 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq333

theorem not_model40_at52 : Not (AssociativeTheory52 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3

theorem not_model40_at53 : Not (AssociativeTheory53 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem not_model40_at54 : Not (AssociativeTheory54 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq411

theorem not_model40_at55 : Not (AssociativeTheory55 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at56 : Not (AssociativeTheory56 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq419

theorem not_model40_at57 : Not (AssociativeTheory57 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq429

theorem not_model40_at58 : Not (AssociativeTheory58 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq440

theorem not_model40_at59 : Not (AssociativeTheory59 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at60 : Not (AssociativeTheory60 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq504

theorem not_model40_at61 : Not (AssociativeTheory61 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq513

theorem not_model40_at62 : Not (AssociativeTheory62 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq440

theorem model40_at63 : AssociativeTheory63 (Fin 8) :=
  ⟨model40_eq3253, model40_eq4512⟩

theorem not_model40_at64 : Not (AssociativeTheory64 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at65 : AssociativeTheory65 (Fin 8) :=
  ⟨model40_eq3255, model40_eq4512⟩

theorem not_model40_at66 : Not (AssociativeTheory66 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem model40_at67 : AssociativeTheory67 (Fin 8) :=
  ⟨model40_eq3256, model40_eq4512⟩

theorem model40_at68 : AssociativeTheory68 (Fin 8) :=
  ⟨model40_eq3258, model40_eq4512⟩

theorem not_model40_at69 : Not (AssociativeTheory69 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem model40_at70 : AssociativeTheory70 (Fin 8) :=
  ⟨model40_eq3255, model40_eq3258, model40_eq4512⟩

theorem model40_at71 : AssociativeTheory71 (Fin 8) :=
  ⟨model40_eq3259, model40_eq4512⟩

theorem model40_at72 : AssociativeTheory72 (Fin 8) :=
  ⟨model40_eq3260, model40_eq4512⟩

theorem model40_at73 : AssociativeTheory73 (Fin 8) :=
  ⟨model40_eq40, model40_eq3260, model40_eq4512⟩

theorem model40_at74 : AssociativeTheory74 (Fin 8) :=
  ⟨model40_eq3261, model40_eq4512⟩

theorem model40_at75 : AssociativeTheory75 (Fin 8) :=
  ⟨model40_eq3264, model40_eq4512⟩

theorem model40_at76 : AssociativeTheory76 (Fin 8) :=
  ⟨model40_eq40, model40_eq3264, model40_eq4512⟩

theorem model40_at77 : AssociativeTheory77 (Fin 8) :=
  ⟨model40_eq308, model40_eq3264, model40_eq4512⟩

theorem model40_at78 : AssociativeTheory78 (Fin 8) :=
  ⟨model40_eq312, model40_eq3264, model40_eq4512⟩

theorem model40_at79 : AssociativeTheory79 (Fin 8) :=
  ⟨model40_eq3260, model40_eq3264, model40_eq4512⟩

theorem model40_at80 : AssociativeTheory80 (Fin 8) :=
  ⟨model40_eq40, model40_eq3260, model40_eq3264, model40_eq4512⟩

theorem model40_at81 : AssociativeTheory81 (Fin 8) :=
  ⟨model40_eq3265, model40_eq4512⟩

theorem model40_at82 : AssociativeTheory82 (Fin 8) :=
  ⟨model40_eq40, model40_eq3265, model40_eq4512⟩

theorem model40_at83 : AssociativeTheory83 (Fin 8) :=
  ⟨model40_eq3260, model40_eq3265, model40_eq4512⟩

theorem model40_at84 : AssociativeTheory84 (Fin 8) :=
  ⟨model40_eq40, model40_eq3260, model40_eq3265, model40_eq4512⟩

theorem model40_at85 : AssociativeTheory85 (Fin 8) :=
  ⟨model40_eq3264, model40_eq3265, model40_eq4512⟩

theorem model40_at86 : AssociativeTheory86 (Fin 8) :=
  ⟨model40_eq40, model40_eq3264, model40_eq3265, model40_eq4512⟩

theorem model40_at87 : AssociativeTheory87 (Fin 8) :=
  ⟨model40_eq3260, model40_eq3264, model40_eq3265, model40_eq4512⟩

theorem model40_at88 : AssociativeTheory88 (Fin 8) :=
  ⟨model40_eq40, model40_eq3260, model40_eq3264, model40_eq3265, model40_eq4512⟩

theorem model40_at89 : AssociativeTheory89 (Fin 8) :=
  ⟨model40_eq3267, model40_eq4512⟩

theorem model40_at90 : AssociativeTheory90 (Fin 8) :=
  ⟨model40_eq40, model40_eq3267, model40_eq4512⟩

theorem not_model40_at91 : Not (AssociativeTheory91 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at92 : AssociativeTheory92 (Fin 8) :=
  ⟨model40_eq309, model40_eq3267, model40_eq4512⟩

theorem model40_at93 : AssociativeTheory93 (Fin 8) :=
  ⟨model40_eq40, model40_eq309, model40_eq3267, model40_eq4512⟩

theorem model40_at94 : AssociativeTheory94 (Fin 8) :=
  ⟨model40_eq3271, model40_eq4512⟩

theorem model40_at95 : AssociativeTheory95 (Fin 8) :=
  ⟨model40_eq3274, model40_eq4512⟩

theorem model40_at96 : AssociativeTheory96 (Fin 8) :=
  ⟨model40_eq3264, model40_eq3274, model40_eq4512⟩

theorem model40_at97 : AssociativeTheory97 (Fin 8) :=
  ⟨model40_eq3278, model40_eq4512⟩

theorem model40_at98 : AssociativeTheory98 (Fin 8) :=
  ⟨model40_eq3292, model40_eq4512⟩

theorem model40_at99 : AssociativeTheory99 (Fin 8) :=
  ⟨model40_eq3264, model40_eq3292, model40_eq4512⟩

theorem model40_at100 : AssociativeTheory100 (Fin 8) :=
  ⟨model40_eq3274, model40_eq3292, model40_eq4512⟩

theorem model40_at101 : AssociativeTheory101 (Fin 8) :=
  ⟨model40_eq3264, model40_eq3274, model40_eq3292, model40_eq4512⟩

theorem model40_at102 : AssociativeTheory102 (Fin 8) :=
  ⟨model40_eq3300, model40_eq4512⟩

theorem model40_at103 : AssociativeTheory103 (Fin 8) :=
  ⟨model40_eq309, model40_eq3300, model40_eq4512⟩

theorem not_model40_at104 : Not (AssociativeTheory104 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at105 : Not (AssociativeTheory105 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at106 : Not (AssociativeTheory106 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at107 : Not (AssociativeTheory107 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at108 : Not (AssociativeTheory108 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at109 : Not (AssociativeTheory109 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at110 : Not (AssociativeTheory110 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at111 : Not (AssociativeTheory111 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3308

theorem not_model40_at112 : Not (AssociativeTheory112 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at113 : Not (AssociativeTheory113 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3315

theorem not_model40_at114 : Not (AssociativeTheory114 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at115 : Not (AssociativeTheory115 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3315

theorem not_model40_at116 : Not (AssociativeTheory116 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at117 : Not (AssociativeTheory117 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3316

theorem not_model40_at118 : Not (AssociativeTheory118 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at119 : Not (AssociativeTheory119 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem not_model40_at120 : Not (AssociativeTheory120 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3319

theorem not_model40_at121 : Not (AssociativeTheory121 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at122 : Not (AssociativeTheory122 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3346

theorem not_model40_at123 : Not (AssociativeTheory123 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at124 : Not (AssociativeTheory124 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3353

theorem not_model40_at125 : Not (AssociativeTheory125 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at126 : Not (AssociativeTheory126 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3319

theorem model40_at127 : AssociativeTheory127 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4512⟩

theorem not_model40_at128 : Not (AssociativeTheory128 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at129 : AssociativeTheory129 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4512⟩

theorem model40_at130 : AssociativeTheory130 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4269, model40_eq4512⟩

theorem model40_at131 : AssociativeTheory131 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4512⟩

theorem not_model40_at132 : Not (AssociativeTheory132 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at133 : AssociativeTheory133 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4270, model40_eq4512⟩

theorem model40_at134 : AssociativeTheory134 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4270, model40_eq4512⟩

theorem model40_at135 : AssociativeTheory135 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4269, model40_eq4270, model40_eq4512⟩

theorem not_model40_at136 : Not (AssociativeTheory136 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4271

theorem not_model40_at137 : Not (AssociativeTheory137 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at138 : AssociativeTheory138 (Fin 8) :=
  ⟨model40_eq4272, model40_eq4512⟩

theorem model40_at139 : AssociativeTheory139 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4272, model40_eq4512⟩

theorem model40_at140 : AssociativeTheory140 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4272, model40_eq4512⟩

theorem model40_at141 : AssociativeTheory141 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4269, model40_eq4272, model40_eq4512⟩

theorem model40_at142 : AssociativeTheory142 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4272, model40_eq4512⟩

theorem model40_at143 : AssociativeTheory143 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4270, model40_eq4272, model40_eq4512⟩

theorem not_model40_at144 : Not (AssociativeTheory144 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4271

theorem model40_at145 : AssociativeTheory145 (Fin 8) :=
  ⟨model40_eq4273, model40_eq4512⟩

theorem model40_at146 : AssociativeTheory146 (Fin 8) :=
  ⟨model40_eq40, model40_eq4273, model40_eq4512⟩

theorem model40_at147 : AssociativeTheory147 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4273, model40_eq4512⟩

theorem model40_at148 : AssociativeTheory148 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4273, model40_eq4512⟩

theorem model40_at149 : AssociativeTheory149 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4273, model40_eq4512⟩

theorem model40_at150 : AssociativeTheory150 (Fin 8) :=
  ⟨model40_eq4275, model40_eq4512⟩

theorem model40_at151 : AssociativeTheory151 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4275, model40_eq4512⟩

theorem model40_at152 : AssociativeTheory152 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4275, model40_eq4512⟩

theorem model40_at153 : AssociativeTheory153 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4275, model40_eq4512⟩

theorem model40_at154 : AssociativeTheory154 (Fin 8) :=
  ⟨model40_eq4272, model40_eq4275, model40_eq4512⟩

theorem model40_at155 : AssociativeTheory155 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4272, model40_eq4275, model40_eq4512⟩

theorem model40_at156 : AssociativeTheory156 (Fin 8) :=
  ⟨model40_eq4273, model40_eq4275, model40_eq4512⟩

theorem model40_at157 : AssociativeTheory157 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4273, model40_eq4275, model40_eq4512⟩

theorem model40_at158 : AssociativeTheory158 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4512⟩

theorem not_model40_at159 : Not (AssociativeTheory159 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem not_model40_at160 : Not (AssociativeTheory160 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4278

theorem model40_at161 : AssociativeTheory161 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4512⟩

theorem not_model40_at162 : Not (AssociativeTheory162 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq47

theorem not_model40_at163 : Not (AssociativeTheory163 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq56

theorem model40_at164 : AssociativeTheory164 (Fin 8) :=
  ⟨model40_eq307, model40_eq4283, model40_eq4512⟩

theorem not_model40_at165 : Not (AssociativeTheory165 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem not_model40_at166 : Not (AssociativeTheory166 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq411

theorem not_model40_at167 : Not (AssociativeTheory167 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq440

theorem model40_at168 : AssociativeTheory168 (Fin 8) :=
  ⟨model40_eq3253, model40_eq4283, model40_eq4512⟩

theorem model40_at169 : AssociativeTheory169 (Fin 8) :=
  ⟨model40_eq3256, model40_eq4283, model40_eq4512⟩

theorem not_model40_at170 : Not (AssociativeTheory170 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3319

theorem model40_at171 : AssociativeTheory171 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4283, model40_eq4512⟩

theorem model40_at172 : AssociativeTheory172 (Fin 8) :=
  ⟨model40_eq4272, model40_eq4283, model40_eq4512⟩

theorem model40_at173 : AssociativeTheory173 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4512⟩

theorem model40_at174 : AssociativeTheory174 (Fin 8) :=
  ⟨model40_eq4284, model40_eq4512⟩

theorem not_model40_at175 : Not (AssociativeTheory175 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at176 : AssociativeTheory176 (Fin 8) :=
  ⟨model40_eq307, model40_eq4284, model40_eq4512⟩

theorem not_model40_at177 : Not (AssociativeTheory177 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at178 : AssociativeTheory178 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4284, model40_eq4512⟩

theorem model40_at179 : AssociativeTheory179 (Fin 8) :=
  ⟨model40_eq4273, model40_eq4284, model40_eq4512⟩

theorem model40_at180 : AssociativeTheory180 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4284, model40_eq4512⟩

theorem not_model40_at181 : Not (AssociativeTheory181 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq43

theorem model40_at182 : AssociativeTheory182 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4284, model40_eq4512⟩

theorem model40_at183 : AssociativeTheory183 (Fin 8) :=
  ⟨model40_eq307, model40_eq4283, model40_eq4284, model40_eq4512⟩

theorem model40_at184 : AssociativeTheory184 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4284, model40_eq4512⟩

theorem not_model40_at185 : Not (AssociativeTheory185 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4287

theorem not_model40_at186 : Not (AssociativeTheory186 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4287

theorem model40_at187 : AssociativeTheory187 (Fin 8) :=
  ⟨model40_eq4290, model40_eq4512⟩

theorem model40_at188 : AssociativeTheory188 (Fin 8) :=
  ⟨model40_eq307, model40_eq4290, model40_eq4512⟩

theorem not_model40_at189 : Not (AssociativeTheory189 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq411

theorem model40_at190 : AssociativeTheory190 (Fin 8) :=
  ⟨model40_eq3253, model40_eq4290, model40_eq4512⟩

theorem model40_at191 : AssociativeTheory191 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4290, model40_eq4512⟩

theorem model40_at192 : AssociativeTheory192 (Fin 8) :=
  ⟨model40_eq4273, model40_eq4290, model40_eq4512⟩

theorem model40_at193 : AssociativeTheory193 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4290, model40_eq4512⟩

theorem model40_at194 : AssociativeTheory194 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4290, model40_eq4512⟩

theorem model40_at195 : AssociativeTheory195 (Fin 8) :=
  ⟨model40_eq307, model40_eq4283, model40_eq4290, model40_eq4512⟩

theorem model40_at196 : AssociativeTheory196 (Fin 8) :=
  ⟨model40_eq3253, model40_eq4283, model40_eq4290, model40_eq4512⟩

theorem model40_at197 : AssociativeTheory197 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4290, model40_eq4512⟩

theorem model40_at198 : AssociativeTheory198 (Fin 8) :=
  ⟨model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at199 : AssociativeTheory199 (Fin 8) :=
  ⟨model40_eq307, model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at200 : AssociativeTheory200 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at201 : AssociativeTheory201 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at202 : AssociativeTheory202 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at203 : AssociativeTheory203 (Fin 8) :=
  ⟨model40_eq307, model40_eq4283, model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at204 : AssociativeTheory204 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4284, model40_eq4290, model40_eq4512⟩

theorem model40_at205 : AssociativeTheory205 (Fin 8) :=
  ⟨model40_eq4291, model40_eq4512⟩

theorem model40_at206 : AssociativeTheory206 (Fin 8) :=
  ⟨model40_eq307, model40_eq4291, model40_eq4512⟩

theorem model40_at207 : AssociativeTheory207 (Fin 8) :=
  ⟨model40_eq312, model40_eq4291, model40_eq4512⟩

theorem not_model40_at208 : Not (AssociativeTheory208 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem model40_at209 : AssociativeTheory209 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4291, model40_eq4512⟩

theorem model40_at210 : AssociativeTheory210 (Fin 8) :=
  ⟨model40_eq4272, model40_eq4291, model40_eq4512⟩

theorem model40_at211 : AssociativeTheory211 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4291, model40_eq4512⟩

theorem model40_at212 : AssociativeTheory212 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4291, model40_eq4512⟩

theorem model40_at213 : AssociativeTheory213 (Fin 8) :=
  ⟨model40_eq307, model40_eq4283, model40_eq4291, model40_eq4512⟩

theorem not_model40_at214 : Not (AssociativeTheory214 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem model40_at215 : AssociativeTheory215 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4283, model40_eq4291, model40_eq4512⟩

theorem model40_at216 : AssociativeTheory216 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4291, model40_eq4512⟩

theorem model40_at217 : AssociativeTheory217 (Fin 8) :=
  ⟨model40_eq4284, model40_eq4291, model40_eq4512⟩

theorem model40_at218 : AssociativeTheory218 (Fin 8) :=
  ⟨model40_eq307, model40_eq4284, model40_eq4291, model40_eq4512⟩

theorem model40_at219 : AssociativeTheory219 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4284, model40_eq4291, model40_eq4512⟩

theorem model40_at220 : AssociativeTheory220 (Fin 8) :=
  ⟨model40_eq4290, model40_eq4291, model40_eq4512⟩

theorem model40_at221 : AssociativeTheory221 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4290, model40_eq4291, model40_eq4512⟩

theorem model40_at222 : AssociativeTheory222 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4512⟩

theorem model40_at223 : AssociativeTheory223 (Fin 8) :=
  ⟨model40_eq307, model40_eq4293, model40_eq4512⟩

theorem model40_at224 : AssociativeTheory224 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4293, model40_eq4512⟩

theorem model40_at225 : AssociativeTheory225 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4293, model40_eq4512⟩

theorem model40_at226 : AssociativeTheory226 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4270, model40_eq4293, model40_eq4512⟩

theorem model40_at227 : AssociativeTheory227 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4512⟩

theorem not_model40_at228 : Not (AssociativeTheory228 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4300

theorem not_model40_at229 : Not (AssociativeTheory229 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4300

theorem model40_at230 : AssociativeTheory230 (Fin 8) :=
  ⟨model40_eq4314, model40_eq4512⟩

theorem model40_at231 : AssociativeTheory231 (Fin 8) :=
  ⟨model40_eq307, model40_eq4314, model40_eq4512⟩

theorem model40_at232 : AssociativeTheory232 (Fin 8) :=
  ⟨model40_eq308, model40_eq4314, model40_eq4512⟩

theorem not_model40_at233 : Not (AssociativeTheory233 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem model40_at234 : AssociativeTheory234 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4314, model40_eq4512⟩

theorem model40_at235 : AssociativeTheory235 (Fin 8) :=
  ⟨model40_eq4275, model40_eq4314, model40_eq4512⟩

theorem model40_at236 : AssociativeTheory236 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4314, model40_eq4512⟩

theorem model40_at237 : AssociativeTheory237 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4314, model40_eq4512⟩

theorem model40_at238 : AssociativeTheory238 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4314, model40_eq4512⟩

theorem not_model40_at239 : Not (AssociativeTheory239 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4315

theorem not_model40_at240 : Not (AssociativeTheory240 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4315

theorem model40_at241 : AssociativeTheory241 (Fin 8) :=
  ⟨model40_eq4320, model40_eq4512⟩

theorem not_model40_at242 : Not (AssociativeTheory242 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq47

theorem not_model40_at243 : Not (AssociativeTheory243 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq75

theorem model40_at244 : AssociativeTheory244 (Fin 8) :=
  ⟨model40_eq307, model40_eq4320, model40_eq4512⟩

theorem not_model40_at245 : Not (AssociativeTheory245 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at246 : Not (AssociativeTheory246 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq411

theorem not_model40_at247 : Not (AssociativeTheory247 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq513

theorem model40_at248 : AssociativeTheory248 (Fin 8) :=
  ⟨model40_eq3253, model40_eq4320, model40_eq4512⟩

theorem model40_at249 : AssociativeTheory249 (Fin 8) :=
  ⟨model40_eq3261, model40_eq4320, model40_eq4512⟩

theorem not_model40_at250 : Not (AssociativeTheory250 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem model40_at251 : AssociativeTheory251 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4320, model40_eq4512⟩

theorem model40_at252 : AssociativeTheory252 (Fin 8) :=
  ⟨model40_eq4275, model40_eq4320, model40_eq4512⟩

theorem model40_at253 : AssociativeTheory253 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4320, model40_eq4512⟩

theorem model40_at254 : AssociativeTheory254 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4320, model40_eq4512⟩

theorem model40_at255 : AssociativeTheory255 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4320, model40_eq4512⟩

theorem model40_at256 : AssociativeTheory256 (Fin 8) :=
  ⟨model40_eq4314, model40_eq4320, model40_eq4512⟩

theorem model40_at257 : AssociativeTheory257 (Fin 8) :=
  ⟨model40_eq307, model40_eq4314, model40_eq4320, model40_eq4512⟩

theorem not_model40_at258 : Not (AssociativeTheory258 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem model40_at259 : AssociativeTheory259 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4314, model40_eq4320, model40_eq4512⟩

theorem model40_at260 : AssociativeTheory260 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4314, model40_eq4320, model40_eq4512⟩

theorem model40_at261 : AssociativeTheory261 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4314, model40_eq4320, model40_eq4512⟩

theorem model40_at262 : AssociativeTheory262 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4314, model40_eq4320, model40_eq4512⟩

theorem model40_at263 : AssociativeTheory263 (Fin 8) :=
  ⟨model40_eq4321, model40_eq4512⟩

theorem model40_at264 : AssociativeTheory264 (Fin 8) :=
  ⟨model40_eq40, model40_eq4321, model40_eq4512⟩

theorem model40_at265 : AssociativeTheory265 (Fin 8) :=
  ⟨model40_eq307, model40_eq4321, model40_eq4512⟩

theorem model40_at266 : AssociativeTheory266 (Fin 8) :=
  ⟨model40_eq3260, model40_eq4321, model40_eq4512⟩

theorem model40_at267 : AssociativeTheory267 (Fin 8) :=
  ⟨model40_eq3265, model40_eq4321, model40_eq4512⟩

theorem model40_at268 : AssociativeTheory268 (Fin 8) :=
  ⟨model40_eq3260, model40_eq3265, model40_eq4321, model40_eq4512⟩

theorem model40_at269 : AssociativeTheory269 (Fin 8) :=
  ⟨model40_eq3267, model40_eq4321, model40_eq4512⟩

theorem model40_at270 : AssociativeTheory270 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4321, model40_eq4512⟩

theorem model40_at271 : AssociativeTheory271 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4321, model40_eq4512⟩

theorem model40_at272 : AssociativeTheory272 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4270, model40_eq4321, model40_eq4512⟩

theorem model40_at273 : AssociativeTheory273 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4321, model40_eq4512⟩

theorem model40_at274 : AssociativeTheory274 (Fin 8) :=
  ⟨model40_eq4284, model40_eq4321, model40_eq4512⟩

theorem model40_at275 : AssociativeTheory275 (Fin 8) :=
  ⟨model40_eq307, model40_eq4284, model40_eq4321, model40_eq4512⟩

theorem model40_at276 : AssociativeTheory276 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4284, model40_eq4321, model40_eq4512⟩

theorem model40_at277 : AssociativeTheory277 (Fin 8) :=
  ⟨model40_eq4290, model40_eq4321, model40_eq4512⟩

theorem model40_at278 : AssociativeTheory278 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4290, model40_eq4321, model40_eq4512⟩

theorem model40_at279 : AssociativeTheory279 (Fin 8) :=
  ⟨model40_eq4284, model40_eq4290, model40_eq4321, model40_eq4512⟩

theorem model40_at280 : AssociativeTheory280 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4284, model40_eq4290, model40_eq4321, model40_eq4512⟩

theorem model40_at281 : AssociativeTheory281 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4321, model40_eq4512⟩

theorem model40_at282 : AssociativeTheory282 (Fin 8) :=
  ⟨model40_eq307, model40_eq4293, model40_eq4321, model40_eq4512⟩

theorem model40_at283 : AssociativeTheory283 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4293, model40_eq4321, model40_eq4512⟩

theorem model40_at284 : AssociativeTheory284 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4321, model40_eq4512⟩

theorem model40_at285 : AssociativeTheory285 (Fin 8) :=
  ⟨model40_eq4343, model40_eq4512⟩

theorem model40_at286 : AssociativeTheory286 (Fin 8) :=
  ⟨model40_eq307, model40_eq4343, model40_eq4512⟩

theorem model40_at287 : AssociativeTheory287 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4343, model40_eq4512⟩

theorem model40_at288 : AssociativeTheory288 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4343, model40_eq4512⟩

theorem model40_at289 : AssociativeTheory289 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4269, model40_eq4343, model40_eq4512⟩

theorem model40_at290 : AssociativeTheory290 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4343, model40_eq4512⟩

theorem model40_at291 : AssociativeTheory291 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4343, model40_eq4512⟩

theorem model40_at292 : AssociativeTheory292 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4343, model40_eq4512⟩

theorem model40_at293 : AssociativeTheory293 (Fin 8) :=
  ⟨model40_eq4291, model40_eq4343, model40_eq4512⟩

theorem model40_at294 : AssociativeTheory294 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4291, model40_eq4343, model40_eq4512⟩

theorem model40_at295 : AssociativeTheory295 (Fin 8) :=
  ⟨model40_eq4283, model40_eq4291, model40_eq4343, model40_eq4512⟩

theorem model40_at296 : AssociativeTheory296 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4283, model40_eq4291, model40_eq4343, model40_eq4512⟩

theorem model40_at297 : AssociativeTheory297 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4343, model40_eq4512⟩

theorem model40_at298 : AssociativeTheory298 (Fin 8) :=
  ⟨model40_eq4269, model40_eq4293, model40_eq4343, model40_eq4512⟩

theorem model40_at299 : AssociativeTheory299 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4343, model40_eq4512⟩

theorem model40_at300 : AssociativeTheory300 (Fin 8) :=
  ⟨model40_eq4321, model40_eq4343, model40_eq4512⟩

theorem model40_at301 : AssociativeTheory301 (Fin 8) :=
  ⟨model40_eq307, model40_eq4321, model40_eq4343, model40_eq4512⟩

theorem model40_at302 : AssociativeTheory302 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4321, model40_eq4343, model40_eq4512⟩

theorem model40_at303 : AssociativeTheory303 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4321, model40_eq4343, model40_eq4512⟩

theorem model40_at304 : AssociativeTheory304 (Fin 8) :=
  ⟨model40_eq4293, model40_eq4321, model40_eq4343, model40_eq4512⟩

theorem model40_at305 : AssociativeTheory305 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4293, model40_eq4321, model40_eq4343, model40_eq4512⟩

theorem not_model40_at306 : Not (AssociativeTheory306 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at307 : Not (AssociativeTheory307 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3

theorem not_model40_at308 : Not (AssociativeTheory308 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at309 : Not (AssociativeTheory309 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at310 : Not (AssociativeTheory310 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq47

theorem not_model40_at311 : Not (AssociativeTheory311 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at312 : Not (AssociativeTheory312 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at313 : Not (AssociativeTheory313 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at314 : Not (AssociativeTheory314 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at315 : Not (AssociativeTheory315 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem not_model40_at316 : Not (AssociativeTheory316 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq411

theorem not_model40_at317 : Not (AssociativeTheory317 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at318 : Not (AssociativeTheory318 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at319 : Not (AssociativeTheory319 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at320 : Not (AssociativeTheory320 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at321 : Not (AssociativeTheory321 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at322 : Not (AssociativeTheory322 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3319

theorem not_model40_at323 : Not (AssociativeTheory323 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at324 : Not (AssociativeTheory324 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at325 : Not (AssociativeTheory325 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at326 : Not (AssociativeTheory326 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at327 : Not (AssociativeTheory327 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at328 : Not (AssociativeTheory328 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at329 : Not (AssociativeTheory329 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at330 : Not (AssociativeTheory330 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at331 : Not (AssociativeTheory331 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at332 : Not (AssociativeTheory332 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at333 : Not (AssociativeTheory333 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at334 : Not (AssociativeTheory334 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at335 : Not (AssociativeTheory335 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at336 : Not (AssociativeTheory336 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at337 : Not (AssociativeTheory337 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at338 : Not (AssociativeTheory338 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at339 : Not (AssociativeTheory339 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at340 : Not (AssociativeTheory340 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at341 : Not (AssociativeTheory341 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at342 : Not (AssociativeTheory342 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at343 : Not (AssociativeTheory343 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at344 : Not (AssociativeTheory344 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at345 : Not (AssociativeTheory345 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at346 : Not (AssociativeTheory346 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at347 : Not (AssociativeTheory347 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at348 : Not (AssociativeTheory348 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at349 : Not (AssociativeTheory349 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at350 : Not (AssociativeTheory350 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at351 : Not (AssociativeTheory351 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at352 : Not (AssociativeTheory352 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3

theorem not_model40_at353 : Not (AssociativeTheory353 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq8

theorem not_model40_at354 : Not (AssociativeTheory354 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at355 : Not (AssociativeTheory355 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq47

theorem not_model40_at356 : Not (AssociativeTheory356 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at357 : Not (AssociativeTheory357 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at358 : Not (AssociativeTheory358 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at359 : Not (AssociativeTheory359 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq323

theorem not_model40_at360 : Not (AssociativeTheory360 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq326

theorem not_model40_at361 : Not (AssociativeTheory361 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq411

theorem not_model40_at362 : Not (AssociativeTheory362 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at363 : Not (AssociativeTheory363 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at364 : Not (AssociativeTheory364 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at365 : Not (AssociativeTheory365 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at366 : Not (AssociativeTheory366 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3306

theorem not_model40_at367 : Not (AssociativeTheory367 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq3319

theorem not_model40_at368 : Not (AssociativeTheory368 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at369 : Not (AssociativeTheory369 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at370 : Not (AssociativeTheory370 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at371 : Not (AssociativeTheory371 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at372 : Not (AssociativeTheory372 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at373 : Not (AssociativeTheory373 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at374 : Not (AssociativeTheory374 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at375 : Not (AssociativeTheory375 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at376 : Not (AssociativeTheory376 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at377 : Not (AssociativeTheory377 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at378 : Not (AssociativeTheory378 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at379 : Not (AssociativeTheory379 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at380 : Not (AssociativeTheory380 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at381 : Not (AssociativeTheory381 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at382 : Not (AssociativeTheory382 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at383 : Not (AssociativeTheory383 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at384 : Not (AssociativeTheory384 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at385 : Not (AssociativeTheory385 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at386 : Not (AssociativeTheory386 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at387 : Not (AssociativeTheory387 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at388 : Not (AssociativeTheory388 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at389 : Not (AssociativeTheory389 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at390 : Not (AssociativeTheory390 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at391 : Not (AssociativeTheory391 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at392 : Not (AssociativeTheory392 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at393 : Not (AssociativeTheory393 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at394 : Not (AssociativeTheory394 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at395 : Not (AssociativeTheory395 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4362

theorem not_model40_at396 : Not (AssociativeTheory396 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at397 : Not (AssociativeTheory397 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at398 : Not (AssociativeTheory398 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at399 : Not (AssociativeTheory399 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at400 : Not (AssociativeTheory400 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at401 : Not (AssociativeTheory401 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at402 : Not (AssociativeTheory402 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at403 : Not (AssociativeTheory403 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at404 : Not (AssociativeTheory404 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at405 : Not (AssociativeTheory405 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at406 : Not (AssociativeTheory406 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem not_model40_at407 : Not (AssociativeTheory407 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4358

theorem model40_at408 : AssociativeTheory408 (Fin 8) :=
  ⟨model40_eq4364, model40_eq4512⟩

theorem model40_at409 : AssociativeTheory409 (Fin 8) :=
  ⟨model40_eq40, model40_eq4364, model40_eq4512⟩

theorem model40_at410 : AssociativeTheory410 (Fin 8) :=
  ⟨model40_eq307, model40_eq4364, model40_eq4512⟩

theorem model40_at411 : AssociativeTheory411 (Fin 8) :=
  ⟨model40_eq40, model40_eq307, model40_eq4364, model40_eq4512⟩

theorem model40_at412 : AssociativeTheory412 (Fin 8) :=
  ⟨model40_eq3253, model40_eq4364, model40_eq4512⟩

theorem model40_at413 : AssociativeTheory413 (Fin 8) :=
  ⟨model40_eq3267, model40_eq4364, model40_eq4512⟩

theorem model40_at414 : AssociativeTheory414 (Fin 8) :=
  ⟨model40_eq4268, model40_eq4364, model40_eq4512⟩

theorem model40_at415 : AssociativeTheory415 (Fin 8) :=
  ⟨model40_eq4270, model40_eq4364, model40_eq4512⟩

theorem model40_at416 : AssociativeTheory416 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4364, model40_eq4512⟩

theorem model40_at417 : AssociativeTheory417 (Fin 8) :=
  ⟨model40_eq4284, model40_eq4364, model40_eq4512⟩

theorem model40_at418 : AssociativeTheory418 (Fin 8) :=
  ⟨model40_eq307, model40_eq4284, model40_eq4364, model40_eq4512⟩

theorem model40_at419 : AssociativeTheory419 (Fin 8) :=
  ⟨model40_eq4276, model40_eq4284, model40_eq4364, model40_eq4512⟩

theorem not_model40_at420 : Not (AssociativeTheory420 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at421 : Not (AssociativeTheory421 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at422 : Not (AssociativeTheory422 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at423 : Not (AssociativeTheory423 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at424 : Not (AssociativeTheory424 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at425 : Not (AssociativeTheory425 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at426 : Not (AssociativeTheory426 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at427 : Not (AssociativeTheory427 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at428 : Not (AssociativeTheory428 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at429 : Not (AssociativeTheory429 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at430 : Not (AssociativeTheory430 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at431 : Not (AssociativeTheory431 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at432 : Not (AssociativeTheory432 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at433 : Not (AssociativeTheory433 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at434 : Not (AssociativeTheory434 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at435 : Not (AssociativeTheory435 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at436 : Not (AssociativeTheory436 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at437 : Not (AssociativeTheory437 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at438 : Not (AssociativeTheory438 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at439 : Not (AssociativeTheory439 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at440 : Not (AssociativeTheory440 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at441 : Not (AssociativeTheory441 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at442 : Not (AssociativeTheory442 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at443 : Not (AssociativeTheory443 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at444 : Not (AssociativeTheory444 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at445 : Not (AssociativeTheory445 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at446 : Not (AssociativeTheory446 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at447 : Not (AssociativeTheory447 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at448 : Not (AssociativeTheory448 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at449 : Not (AssociativeTheory449 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at450 : Not (AssociativeTheory450 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at451 : Not (AssociativeTheory451 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at452 : Not (AssociativeTheory452 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at453 : Not (AssociativeTheory453 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at454 : Not (AssociativeTheory454 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at455 : Not (AssociativeTheory455 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369

theorem not_model40_at456 : Not (AssociativeTheory456 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model40_eq4369
