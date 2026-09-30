import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model24_op := finOpTable "[[1,1,5,4,1,1],[1,1,1,1,1,1],[3,1,1,1,1,4],[1,1,4,1,1,1],[1,1,1,1,1,1],[4,1,1,1,1,1]]"
private def model24 : Magma (Fin 6) where op := model24_op
private instance : Magma (Fin 6) := model24

private theorem model24_eq1 : Equation1 (Fin 6) := by decideFin!
private theorem model24_eq40 : Equation40 (Fin 6) := by decideFin!
private theorem model24_eq307 : Equation307 (Fin 6) := by decideFin!
private theorem model24_eq308 : Equation308 (Fin 6) := by decideFin!
private theorem model24_eq310 : Equation310 (Fin 6) := by decideFin!
private theorem model24_eq312 : Equation312 (Fin 6) := by decideFin!
private theorem model24_eq315 : Equation315 (Fin 6) := by decideFin!
private theorem model24_eq316 : Equation316 (Fin 6) := by decideFin!
private theorem model24_eq3253 : Equation3253 (Fin 6) := by decideFin!
private theorem model24_eq3255 : Equation3255 (Fin 6) := by decideFin!
private theorem model24_eq3256 : Equation3256 (Fin 6) := by decideFin!
private theorem model24_eq3258 : Equation3258 (Fin 6) := by decideFin!
private theorem model24_eq3259 : Equation3259 (Fin 6) := by decideFin!
private theorem model24_eq3260 : Equation3260 (Fin 6) := by decideFin!
private theorem model24_eq3261 : Equation3261 (Fin 6) := by decideFin!
private theorem model24_eq3264 : Equation3264 (Fin 6) := by decideFin!
private theorem model24_eq3265 : Equation3265 (Fin 6) := by decideFin!
private theorem model24_eq3267 : Equation3267 (Fin 6) := by decideFin!
private theorem model24_eq3271 : Equation3271 (Fin 6) := by decideFin!
private theorem model24_eq3273 : Equation3273 (Fin 6) := by decideFin!
private theorem model24_eq3274 : Equation3274 (Fin 6) := by decideFin!
private theorem model24_eq3275 : Equation3275 (Fin 6) := by decideFin!
private theorem model24_eq3277 : Equation3277 (Fin 6) := by decideFin!
private theorem model24_eq3278 : Equation3278 (Fin 6) := by decideFin!
private theorem model24_eq3290 : Equation3290 (Fin 6) := by decideFin!
private theorem model24_eq3292 : Equation3292 (Fin 6) := by decideFin!
private theorem model24_eq3300 : Equation3300 (Fin 6) := by decideFin!
private theorem model24_eq4268 : Equation4268 (Fin 6) := by decideFin!
private theorem model24_eq4270 : Equation4270 (Fin 6) := by decideFin!
private theorem model24_eq4272 : Equation4272 (Fin 6) := by decideFin!
private theorem model24_eq4275 : Equation4275 (Fin 6) := by decideFin!
private theorem model24_eq4276 : Equation4276 (Fin 6) := by decideFin!
private theorem model24_eq4277 : Equation4277 (Fin 6) := by decideFin!
private theorem model24_eq4280 : Equation4280 (Fin 6) := by decideFin!
private theorem model24_eq4284 : Equation4284 (Fin 6) := by decideFin!
private theorem model24_eq4288 : Equation4288 (Fin 6) := by decideFin!
private theorem model24_eq4290 : Equation4290 (Fin 6) := by decideFin!
private theorem model24_eq4293 : Equation4293 (Fin 6) := by decideFin!
private theorem model24_eq4297 : Equation4297 (Fin 6) := by decideFin!
private theorem model24_eq4299 : Equation4299 (Fin 6) := by decideFin!
private theorem model24_eq4304 : Equation4304 (Fin 6) := by decideFin!
private theorem model24_eq4321 : Equation4321 (Fin 6) := by decideFin!
private theorem model24_eq4343 : Equation4343 (Fin 6) := by decideFin!
private theorem model24_eq4369 : Equation4369 (Fin 6) := by decideFin!
private theorem model24_eq4512 : Equation4512 (Fin 6) := by decideFin!
private theorem not_model24_eq2 : Not (Equation2 (Fin 6)) := by decideFin!
private theorem not_model24_eq3 : Not (Equation3 (Fin 6)) := by decideFin!
private theorem not_model24_eq4 : Not (Equation4 (Fin 6)) := by decideFin!
private theorem not_model24_eq5 : Not (Equation5 (Fin 6)) := by decideFin!
private theorem not_model24_eq8 : Not (Equation8 (Fin 6)) := by decideFin!
private theorem not_model24_eq10 : Not (Equation10 (Fin 6)) := by decideFin!
private theorem not_model24_eq11 : Not (Equation11 (Fin 6)) := by decideFin!
private theorem not_model24_eq14 : Not (Equation14 (Fin 6)) := by decideFin!
private theorem not_model24_eq16 : Not (Equation16 (Fin 6)) := by decideFin!
private theorem not_model24_eq38 : Not (Equation38 (Fin 6)) := by decideFin!
private theorem not_model24_eq39 : Not (Equation39 (Fin 6)) := by decideFin!
private theorem not_model24_eq41 : Not (Equation41 (Fin 6)) := by decideFin!
private theorem not_model24_eq43 : Not (Equation43 (Fin 6)) := by decideFin!
private theorem not_model24_eq47 : Not (Equation47 (Fin 6)) := by decideFin!
private theorem not_model24_eq56 : Not (Equation56 (Fin 6)) := by decideFin!
private theorem not_model24_eq66 : Not (Equation66 (Fin 6)) := by decideFin!
private theorem not_model24_eq75 : Not (Equation75 (Fin 6)) := by decideFin!
private theorem not_model24_eq309 : Not (Equation309 (Fin 6)) := by decideFin!
private theorem not_model24_eq311 : Not (Equation311 (Fin 6)) := by decideFin!
private theorem not_model24_eq313 : Not (Equation313 (Fin 6)) := by decideFin!
private theorem not_model24_eq314 : Not (Equation314 (Fin 6)) := by decideFin!
private theorem not_model24_eq318 : Not (Equation318 (Fin 6)) := by decideFin!
private theorem not_model24_eq323 : Not (Equation323 (Fin 6)) := by decideFin!
private theorem not_model24_eq325 : Not (Equation325 (Fin 6)) := by decideFin!
private theorem not_model24_eq326 : Not (Equation326 (Fin 6)) := by decideFin!
private theorem not_model24_eq327 : Not (Equation327 (Fin 6)) := by decideFin!
private theorem not_model24_eq329 : Not (Equation329 (Fin 6)) := by decideFin!
private theorem not_model24_eq332 : Not (Equation332 (Fin 6)) := by decideFin!
private theorem not_model24_eq333 : Not (Equation333 (Fin 6)) := by decideFin!
private theorem not_model24_eq343 : Not (Equation343 (Fin 6)) := by decideFin!
private theorem not_model24_eq411 : Not (Equation411 (Fin 6)) := by decideFin!
private theorem not_model24_eq419 : Not (Equation419 (Fin 6)) := by decideFin!
private theorem not_model24_eq429 : Not (Equation429 (Fin 6)) := by decideFin!
private theorem not_model24_eq440 : Not (Equation440 (Fin 6)) := by decideFin!
private theorem not_model24_eq477 : Not (Equation477 (Fin 6)) := by decideFin!
private theorem not_model24_eq504 : Not (Equation504 (Fin 6)) := by decideFin!
private theorem not_model24_eq513 : Not (Equation513 (Fin 6)) := by decideFin!
private theorem not_model24_eq3306 : Not (Equation3306 (Fin 6)) := by decideFin!
private theorem not_model24_eq3308 : Not (Equation3308 (Fin 6)) := by decideFin!
private theorem not_model24_eq3309 : Not (Equation3309 (Fin 6)) := by decideFin!
private theorem not_model24_eq3315 : Not (Equation3315 (Fin 6)) := by decideFin!
private theorem not_model24_eq3316 : Not (Equation3316 (Fin 6)) := by decideFin!
private theorem not_model24_eq3319 : Not (Equation3319 (Fin 6)) := by decideFin!
private theorem not_model24_eq3322 : Not (Equation3322 (Fin 6)) := by decideFin!
private theorem not_model24_eq3323 : Not (Equation3323 (Fin 6)) := by decideFin!
private theorem not_model24_eq3326 : Not (Equation3326 (Fin 6)) := by decideFin!
private theorem not_model24_eq3331 : Not (Equation3331 (Fin 6)) := by decideFin!
private theorem not_model24_eq3334 : Not (Equation3334 (Fin 6)) := by decideFin!
private theorem not_model24_eq3342 : Not (Equation3342 (Fin 6)) := by decideFin!
private theorem not_model24_eq3346 : Not (Equation3346 (Fin 6)) := by decideFin!
private theorem not_model24_eq3350 : Not (Equation3350 (Fin 6)) := by decideFin!
private theorem not_model24_eq3353 : Not (Equation3353 (Fin 6)) := by decideFin!
private theorem not_model24_eq3388 : Not (Equation3388 (Fin 6)) := by decideFin!
private theorem not_model24_eq3414 : Not (Equation3414 (Fin 6)) := by decideFin!
private theorem not_model24_eq4269 : Not (Equation4269 (Fin 6)) := by decideFin!
private theorem not_model24_eq4271 : Not (Equation4271 (Fin 6)) := by decideFin!
private theorem not_model24_eq4273 : Not (Equation4273 (Fin 6)) := by decideFin!
private theorem not_model24_eq4274 : Not (Equation4274 (Fin 6)) := by decideFin!
private theorem not_model24_eq4278 : Not (Equation4278 (Fin 6)) := by decideFin!
private theorem not_model24_eq4279 : Not (Equation4279 (Fin 6)) := by decideFin!
private theorem not_model24_eq4283 : Not (Equation4283 (Fin 6)) := by decideFin!
private theorem not_model24_eq4286 : Not (Equation4286 (Fin 6)) := by decideFin!
private theorem not_model24_eq4287 : Not (Equation4287 (Fin 6)) := by decideFin!
private theorem not_model24_eq4291 : Not (Equation4291 (Fin 6)) := by decideFin!
private theorem not_model24_eq4296 : Not (Equation4296 (Fin 6)) := by decideFin!
private theorem not_model24_eq4300 : Not (Equation4300 (Fin 6)) := by decideFin!
private theorem not_model24_eq4301 : Not (Equation4301 (Fin 6)) := by decideFin!
private theorem not_model24_eq4305 : Not (Equation4305 (Fin 6)) := by decideFin!
private theorem not_model24_eq4314 : Not (Equation4314 (Fin 6)) := by decideFin!
private theorem not_model24_eq4315 : Not (Equation4315 (Fin 6)) := by decideFin!
private theorem not_model24_eq4318 : Not (Equation4318 (Fin 6)) := by decideFin!
private theorem not_model24_eq4320 : Not (Equation4320 (Fin 6)) := by decideFin!
private theorem not_model24_eq4325 : Not (Equation4325 (Fin 6)) := by decideFin!
private theorem not_model24_eq4327 : Not (Equation4327 (Fin 6)) := by decideFin!
private theorem not_model24_eq4331 : Not (Equation4331 (Fin 6)) := by decideFin!
private theorem not_model24_eq4358 : Not (Equation4358 (Fin 6)) := by decideFin!
private theorem not_model24_eq4362 : Not (Equation4362 (Fin 6)) := by decideFin!
private theorem not_model24_eq4364 : Not (Equation4364 (Fin 6)) := by decideFin!

theorem model24_at1 : AssociativeTheory1 (Fin 6) :=
  model24_eq4512

theorem not_model24_at2 : Not (AssociativeTheory2 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq2

theorem not_model24_at3 : Not (AssociativeTheory3 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3

theorem not_model24_at4 : Not (AssociativeTheory4 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4

theorem not_model24_at5 : Not (AssociativeTheory5 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq5

theorem not_model24_at6 : Not (AssociativeTheory6 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at7 : Not (AssociativeTheory7 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq10

theorem not_model24_at8 : Not (AssociativeTheory8 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq11

theorem not_model24_at9 : Not (AssociativeTheory9 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq14

theorem not_model24_at10 : Not (AssociativeTheory10 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq16

theorem not_model24_at11 : Not (AssociativeTheory11 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq38

theorem not_model24_at12 : Not (AssociativeTheory12 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq39

theorem not_model24_at13 : Not (AssociativeTheory13 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq38

theorem model24_at14 : AssociativeTheory14 (Fin 6) :=
  ⟨model24_eq40, model24_eq4512⟩

theorem not_model24_at15 : Not (AssociativeTheory15 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at16 : Not (AssociativeTheory16 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3

theorem not_model24_at17 : Not (AssociativeTheory17 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at18 : Not (AssociativeTheory18 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at19 : Not (AssociativeTheory19 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq47

theorem not_model24_at20 : Not (AssociativeTheory20 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at21 : Not (AssociativeTheory21 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq56

theorem not_model24_at22 : Not (AssociativeTheory22 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at23 : Not (AssociativeTheory23 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq75

theorem not_model24_at24 : Not (AssociativeTheory24 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq56

theorem model24_at25 : AssociativeTheory25 (Fin 6) :=
  ⟨model24_eq307, model24_eq4512⟩

theorem model24_at26 : AssociativeTheory26 (Fin 6) :=
  ⟨model24_eq40, model24_eq307, model24_eq4512⟩

theorem not_model24_at27 : Not (AssociativeTheory27 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at28 : Not (AssociativeTheory28 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem model24_at29 : AssociativeTheory29 (Fin 6) :=
  ⟨model24_eq308, model24_eq4512⟩

theorem not_model24_at30 : Not (AssociativeTheory30 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem not_model24_at31 : Not (AssociativeTheory31 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem not_model24_at32 : Not (AssociativeTheory32 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem model24_at33 : AssociativeTheory33 (Fin 6) :=
  ⟨model24_eq310, model24_eq4512⟩

theorem not_model24_at34 : Not (AssociativeTheory34 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq311

theorem not_model24_at35 : Not (AssociativeTheory35 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq311

theorem not_model24_at36 : Not (AssociativeTheory36 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem model24_at37 : AssociativeTheory37 (Fin 6) :=
  ⟨model24_eq312, model24_eq4512⟩

theorem not_model24_at38 : Not (AssociativeTheory38 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem model24_at39 : AssociativeTheory39 (Fin 6) :=
  ⟨model24_eq315, model24_eq4512⟩

theorem not_model24_at40 : Not (AssociativeTheory40 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq318

theorem not_model24_at41 : Not (AssociativeTheory41 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at42 : Not (AssociativeTheory42 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at43 : Not (AssociativeTheory43 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem not_model24_at44 : Not (AssociativeTheory44 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at45 : Not (AssociativeTheory45 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq325

theorem not_model24_at46 : Not (AssociativeTheory46 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3

theorem not_model24_at47 : Not (AssociativeTheory47 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq325

theorem not_model24_at48 : Not (AssociativeTheory48 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at49 : Not (AssociativeTheory49 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at50 : Not (AssociativeTheory50 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at51 : Not (AssociativeTheory51 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq333

theorem not_model24_at52 : Not (AssociativeTheory52 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3

theorem not_model24_at53 : Not (AssociativeTheory53 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at54 : Not (AssociativeTheory54 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq411

theorem not_model24_at55 : Not (AssociativeTheory55 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at56 : Not (AssociativeTheory56 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq419

theorem not_model24_at57 : Not (AssociativeTheory57 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq429

theorem not_model24_at58 : Not (AssociativeTheory58 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq440

theorem not_model24_at59 : Not (AssociativeTheory59 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at60 : Not (AssociativeTheory60 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq504

theorem not_model24_at61 : Not (AssociativeTheory61 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq513

theorem not_model24_at62 : Not (AssociativeTheory62 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq440

theorem model24_at63 : AssociativeTheory63 (Fin 6) :=
  ⟨model24_eq3253, model24_eq4512⟩

theorem not_model24_at64 : Not (AssociativeTheory64 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem model24_at65 : AssociativeTheory65 (Fin 6) :=
  ⟨model24_eq3255, model24_eq4512⟩

theorem not_model24_at66 : Not (AssociativeTheory66 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem model24_at67 : AssociativeTheory67 (Fin 6) :=
  ⟨model24_eq3256, model24_eq4512⟩

theorem model24_at68 : AssociativeTheory68 (Fin 6) :=
  ⟨model24_eq3258, model24_eq4512⟩

theorem not_model24_at69 : Not (AssociativeTheory69 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem model24_at70 : AssociativeTheory70 (Fin 6) :=
  ⟨model24_eq3255, model24_eq3258, model24_eq4512⟩

theorem model24_at71 : AssociativeTheory71 (Fin 6) :=
  ⟨model24_eq3259, model24_eq4512⟩

theorem model24_at72 : AssociativeTheory72 (Fin 6) :=
  ⟨model24_eq3260, model24_eq4512⟩

theorem model24_at73 : AssociativeTheory73 (Fin 6) :=
  ⟨model24_eq40, model24_eq3260, model24_eq4512⟩

theorem model24_at74 : AssociativeTheory74 (Fin 6) :=
  ⟨model24_eq3261, model24_eq4512⟩

theorem model24_at75 : AssociativeTheory75 (Fin 6) :=
  ⟨model24_eq3264, model24_eq4512⟩

theorem model24_at76 : AssociativeTheory76 (Fin 6) :=
  ⟨model24_eq40, model24_eq3264, model24_eq4512⟩

theorem model24_at77 : AssociativeTheory77 (Fin 6) :=
  ⟨model24_eq308, model24_eq3264, model24_eq4512⟩

theorem model24_at78 : AssociativeTheory78 (Fin 6) :=
  ⟨model24_eq312, model24_eq3264, model24_eq4512⟩

theorem model24_at79 : AssociativeTheory79 (Fin 6) :=
  ⟨model24_eq3260, model24_eq3264, model24_eq4512⟩

theorem model24_at80 : AssociativeTheory80 (Fin 6) :=
  ⟨model24_eq40, model24_eq3260, model24_eq3264, model24_eq4512⟩

theorem model24_at81 : AssociativeTheory81 (Fin 6) :=
  ⟨model24_eq3265, model24_eq4512⟩

theorem model24_at82 : AssociativeTheory82 (Fin 6) :=
  ⟨model24_eq40, model24_eq3265, model24_eq4512⟩

theorem model24_at83 : AssociativeTheory83 (Fin 6) :=
  ⟨model24_eq3260, model24_eq3265, model24_eq4512⟩

theorem model24_at84 : AssociativeTheory84 (Fin 6) :=
  ⟨model24_eq40, model24_eq3260, model24_eq3265, model24_eq4512⟩

theorem model24_at85 : AssociativeTheory85 (Fin 6) :=
  ⟨model24_eq3264, model24_eq3265, model24_eq4512⟩

theorem model24_at86 : AssociativeTheory86 (Fin 6) :=
  ⟨model24_eq40, model24_eq3264, model24_eq3265, model24_eq4512⟩

theorem model24_at87 : AssociativeTheory87 (Fin 6) :=
  ⟨model24_eq3260, model24_eq3264, model24_eq3265, model24_eq4512⟩

theorem model24_at88 : AssociativeTheory88 (Fin 6) :=
  ⟨model24_eq40, model24_eq3260, model24_eq3264, model24_eq3265, model24_eq4512⟩

theorem model24_at89 : AssociativeTheory89 (Fin 6) :=
  ⟨model24_eq3267, model24_eq4512⟩

theorem model24_at90 : AssociativeTheory90 (Fin 6) :=
  ⟨model24_eq40, model24_eq3267, model24_eq4512⟩

theorem not_model24_at91 : Not (AssociativeTheory91 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at92 : Not (AssociativeTheory92 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem not_model24_at93 : Not (AssociativeTheory93 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem model24_at94 : AssociativeTheory94 (Fin 6) :=
  ⟨model24_eq3271, model24_eq4512⟩

theorem model24_at95 : AssociativeTheory95 (Fin 6) :=
  ⟨model24_eq3274, model24_eq4512⟩

theorem model24_at96 : AssociativeTheory96 (Fin 6) :=
  ⟨model24_eq3264, model24_eq3274, model24_eq4512⟩

theorem model24_at97 : AssociativeTheory97 (Fin 6) :=
  ⟨model24_eq3278, model24_eq4512⟩

theorem model24_at98 : AssociativeTheory98 (Fin 6) :=
  ⟨model24_eq3292, model24_eq4512⟩

theorem model24_at99 : AssociativeTheory99 (Fin 6) :=
  ⟨model24_eq3264, model24_eq3292, model24_eq4512⟩

theorem model24_at100 : AssociativeTheory100 (Fin 6) :=
  ⟨model24_eq3274, model24_eq3292, model24_eq4512⟩

theorem model24_at101 : AssociativeTheory101 (Fin 6) :=
  ⟨model24_eq3264, model24_eq3274, model24_eq3292, model24_eq4512⟩

theorem model24_at102 : AssociativeTheory102 (Fin 6) :=
  ⟨model24_eq3300, model24_eq4512⟩

theorem not_model24_at103 : Not (AssociativeTheory103 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem not_model24_at104 : Not (AssociativeTheory104 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at105 : Not (AssociativeTheory105 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at106 : Not (AssociativeTheory106 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at107 : Not (AssociativeTheory107 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at108 : Not (AssociativeTheory108 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at109 : Not (AssociativeTheory109 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at110 : Not (AssociativeTheory110 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at111 : Not (AssociativeTheory111 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3308

theorem not_model24_at112 : Not (AssociativeTheory112 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at113 : Not (AssociativeTheory113 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3315

theorem not_model24_at114 : Not (AssociativeTheory114 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at115 : Not (AssociativeTheory115 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3315

theorem not_model24_at116 : Not (AssociativeTheory116 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at117 : Not (AssociativeTheory117 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3316

theorem not_model24_at118 : Not (AssociativeTheory118 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at119 : Not (AssociativeTheory119 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at120 : Not (AssociativeTheory120 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3319

theorem not_model24_at121 : Not (AssociativeTheory121 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at122 : Not (AssociativeTheory122 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3346

theorem not_model24_at123 : Not (AssociativeTheory123 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at124 : Not (AssociativeTheory124 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3353

theorem not_model24_at125 : Not (AssociativeTheory125 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at126 : Not (AssociativeTheory126 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3319

theorem model24_at127 : AssociativeTheory127 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4512⟩

theorem not_model24_at128 : Not (AssociativeTheory128 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at129 : Not (AssociativeTheory129 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at130 : Not (AssociativeTheory130 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at131 : AssociativeTheory131 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4512⟩

theorem not_model24_at132 : Not (AssociativeTheory132 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem model24_at133 : AssociativeTheory133 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4270, model24_eq4512⟩

theorem not_model24_at134 : Not (AssociativeTheory134 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at135 : Not (AssociativeTheory135 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at136 : Not (AssociativeTheory136 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4271

theorem not_model24_at137 : Not (AssociativeTheory137 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem model24_at138 : AssociativeTheory138 (Fin 6) :=
  ⟨model24_eq4272, model24_eq4512⟩

theorem model24_at139 : AssociativeTheory139 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4272, model24_eq4512⟩

theorem not_model24_at140 : Not (AssociativeTheory140 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at141 : Not (AssociativeTheory141 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at142 : AssociativeTheory142 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4272, model24_eq4512⟩

theorem not_model24_at143 : Not (AssociativeTheory143 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at144 : Not (AssociativeTheory144 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4271

theorem not_model24_at145 : Not (AssociativeTheory145 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at146 : Not (AssociativeTheory146 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at147 : Not (AssociativeTheory147 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at148 : Not (AssociativeTheory148 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at149 : Not (AssociativeTheory149 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem model24_at150 : AssociativeTheory150 (Fin 6) :=
  ⟨model24_eq4275, model24_eq4512⟩

theorem model24_at151 : AssociativeTheory151 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4275, model24_eq4512⟩

theorem not_model24_at152 : Not (AssociativeTheory152 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at153 : AssociativeTheory153 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4275, model24_eq4512⟩

theorem model24_at154 : AssociativeTheory154 (Fin 6) :=
  ⟨model24_eq4272, model24_eq4275, model24_eq4512⟩

theorem not_model24_at155 : Not (AssociativeTheory155 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at156 : Not (AssociativeTheory156 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at157 : Not (AssociativeTheory157 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem model24_at158 : AssociativeTheory158 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4512⟩

theorem not_model24_at159 : Not (AssociativeTheory159 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at160 : Not (AssociativeTheory160 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4278

theorem not_model24_at161 : Not (AssociativeTheory161 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at162 : Not (AssociativeTheory162 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq47

theorem not_model24_at163 : Not (AssociativeTheory163 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq56

theorem not_model24_at164 : Not (AssociativeTheory164 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at165 : Not (AssociativeTheory165 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at166 : Not (AssociativeTheory166 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq411

theorem not_model24_at167 : Not (AssociativeTheory167 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq440

theorem not_model24_at168 : Not (AssociativeTheory168 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at169 : Not (AssociativeTheory169 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at170 : Not (AssociativeTheory170 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3319

theorem not_model24_at171 : Not (AssociativeTheory171 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at172 : Not (AssociativeTheory172 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at173 : Not (AssociativeTheory173 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem model24_at174 : AssociativeTheory174 (Fin 6) :=
  ⟨model24_eq4284, model24_eq4512⟩

theorem not_model24_at175 : Not (AssociativeTheory175 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem model24_at176 : AssociativeTheory176 (Fin 6) :=
  ⟨model24_eq307, model24_eq4284, model24_eq4512⟩

theorem not_model24_at177 : Not (AssociativeTheory177 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at178 : Not (AssociativeTheory178 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at179 : Not (AssociativeTheory179 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem model24_at180 : AssociativeTheory180 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4284, model24_eq4512⟩

theorem not_model24_at181 : Not (AssociativeTheory181 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq43

theorem not_model24_at182 : Not (AssociativeTheory182 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at183 : Not (AssociativeTheory183 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at184 : Not (AssociativeTheory184 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at185 : Not (AssociativeTheory185 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4287

theorem not_model24_at186 : Not (AssociativeTheory186 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4287

theorem model24_at187 : AssociativeTheory187 (Fin 6) :=
  ⟨model24_eq4290, model24_eq4512⟩

theorem model24_at188 : AssociativeTheory188 (Fin 6) :=
  ⟨model24_eq307, model24_eq4290, model24_eq4512⟩

theorem not_model24_at189 : Not (AssociativeTheory189 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq411

theorem model24_at190 : AssociativeTheory190 (Fin 6) :=
  ⟨model24_eq3253, model24_eq4290, model24_eq4512⟩

theorem not_model24_at191 : Not (AssociativeTheory191 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at192 : Not (AssociativeTheory192 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem model24_at193 : AssociativeTheory193 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4290, model24_eq4512⟩

theorem not_model24_at194 : Not (AssociativeTheory194 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at195 : Not (AssociativeTheory195 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at196 : Not (AssociativeTheory196 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at197 : Not (AssociativeTheory197 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem model24_at198 : AssociativeTheory198 (Fin 6) :=
  ⟨model24_eq4284, model24_eq4290, model24_eq4512⟩

theorem model24_at199 : AssociativeTheory199 (Fin 6) :=
  ⟨model24_eq307, model24_eq4284, model24_eq4290, model24_eq4512⟩

theorem not_model24_at200 : Not (AssociativeTheory200 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at201 : AssociativeTheory201 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4284, model24_eq4290, model24_eq4512⟩

theorem not_model24_at202 : Not (AssociativeTheory202 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at203 : Not (AssociativeTheory203 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at204 : Not (AssociativeTheory204 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at205 : Not (AssociativeTheory205 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at206 : Not (AssociativeTheory206 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at207 : Not (AssociativeTheory207 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at208 : Not (AssociativeTheory208 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at209 : Not (AssociativeTheory209 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at210 : Not (AssociativeTheory210 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at211 : Not (AssociativeTheory211 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at212 : Not (AssociativeTheory212 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at213 : Not (AssociativeTheory213 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at214 : Not (AssociativeTheory214 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at215 : Not (AssociativeTheory215 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at216 : Not (AssociativeTheory216 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at217 : Not (AssociativeTheory217 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at218 : Not (AssociativeTheory218 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at219 : Not (AssociativeTheory219 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at220 : Not (AssociativeTheory220 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at221 : Not (AssociativeTheory221 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem model24_at222 : AssociativeTheory222 (Fin 6) :=
  ⟨model24_eq4293, model24_eq4512⟩

theorem model24_at223 : AssociativeTheory223 (Fin 6) :=
  ⟨model24_eq307, model24_eq4293, model24_eq4512⟩

theorem not_model24_at224 : Not (AssociativeTheory224 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at225 : AssociativeTheory225 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4293, model24_eq4512⟩

theorem not_model24_at226 : Not (AssociativeTheory226 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at227 : AssociativeTheory227 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4293, model24_eq4512⟩

theorem not_model24_at228 : Not (AssociativeTheory228 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4300

theorem not_model24_at229 : Not (AssociativeTheory229 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4300

theorem not_model24_at230 : Not (AssociativeTheory230 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at231 : Not (AssociativeTheory231 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at232 : Not (AssociativeTheory232 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at233 : Not (AssociativeTheory233 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at234 : Not (AssociativeTheory234 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at235 : Not (AssociativeTheory235 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at236 : Not (AssociativeTheory236 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at237 : Not (AssociativeTheory237 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at238 : Not (AssociativeTheory238 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at239 : Not (AssociativeTheory239 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4315

theorem not_model24_at240 : Not (AssociativeTheory240 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4315

theorem not_model24_at241 : Not (AssociativeTheory241 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at242 : Not (AssociativeTheory242 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq47

theorem not_model24_at243 : Not (AssociativeTheory243 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq75

theorem not_model24_at244 : Not (AssociativeTheory244 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at245 : Not (AssociativeTheory245 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at246 : Not (AssociativeTheory246 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq411

theorem not_model24_at247 : Not (AssociativeTheory247 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq513

theorem not_model24_at248 : Not (AssociativeTheory248 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at249 : Not (AssociativeTheory249 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at250 : Not (AssociativeTheory250 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at251 : Not (AssociativeTheory251 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at252 : Not (AssociativeTheory252 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at253 : Not (AssociativeTheory253 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at254 : Not (AssociativeTheory254 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at255 : Not (AssociativeTheory255 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4320

theorem not_model24_at256 : Not (AssociativeTheory256 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at257 : Not (AssociativeTheory257 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at258 : Not (AssociativeTheory258 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at259 : Not (AssociativeTheory259 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at260 : Not (AssociativeTheory260 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at261 : Not (AssociativeTheory261 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at262 : Not (AssociativeTheory262 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem model24_at263 : AssociativeTheory263 (Fin 6) :=
  ⟨model24_eq4321, model24_eq4512⟩

theorem model24_at264 : AssociativeTheory264 (Fin 6) :=
  ⟨model24_eq40, model24_eq4321, model24_eq4512⟩

theorem model24_at265 : AssociativeTheory265 (Fin 6) :=
  ⟨model24_eq307, model24_eq4321, model24_eq4512⟩

theorem model24_at266 : AssociativeTheory266 (Fin 6) :=
  ⟨model24_eq3260, model24_eq4321, model24_eq4512⟩

theorem model24_at267 : AssociativeTheory267 (Fin 6) :=
  ⟨model24_eq3265, model24_eq4321, model24_eq4512⟩

theorem model24_at268 : AssociativeTheory268 (Fin 6) :=
  ⟨model24_eq3260, model24_eq3265, model24_eq4321, model24_eq4512⟩

theorem model24_at269 : AssociativeTheory269 (Fin 6) :=
  ⟨model24_eq3267, model24_eq4321, model24_eq4512⟩

theorem model24_at270 : AssociativeTheory270 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4321, model24_eq4512⟩

theorem model24_at271 : AssociativeTheory271 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4321, model24_eq4512⟩

theorem model24_at272 : AssociativeTheory272 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4270, model24_eq4321, model24_eq4512⟩

theorem model24_at273 : AssociativeTheory273 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4321, model24_eq4512⟩

theorem model24_at274 : AssociativeTheory274 (Fin 6) :=
  ⟨model24_eq4284, model24_eq4321, model24_eq4512⟩

theorem model24_at275 : AssociativeTheory275 (Fin 6) :=
  ⟨model24_eq307, model24_eq4284, model24_eq4321, model24_eq4512⟩

theorem model24_at276 : AssociativeTheory276 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4284, model24_eq4321, model24_eq4512⟩

theorem model24_at277 : AssociativeTheory277 (Fin 6) :=
  ⟨model24_eq4290, model24_eq4321, model24_eq4512⟩

theorem model24_at278 : AssociativeTheory278 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4290, model24_eq4321, model24_eq4512⟩

theorem model24_at279 : AssociativeTheory279 (Fin 6) :=
  ⟨model24_eq4284, model24_eq4290, model24_eq4321, model24_eq4512⟩

theorem model24_at280 : AssociativeTheory280 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4284, model24_eq4290, model24_eq4321, model24_eq4512⟩

theorem model24_at281 : AssociativeTheory281 (Fin 6) :=
  ⟨model24_eq4293, model24_eq4321, model24_eq4512⟩

theorem model24_at282 : AssociativeTheory282 (Fin 6) :=
  ⟨model24_eq307, model24_eq4293, model24_eq4321, model24_eq4512⟩

theorem model24_at283 : AssociativeTheory283 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4293, model24_eq4321, model24_eq4512⟩

theorem model24_at284 : AssociativeTheory284 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4293, model24_eq4321, model24_eq4512⟩

theorem model24_at285 : AssociativeTheory285 (Fin 6) :=
  ⟨model24_eq4343, model24_eq4512⟩

theorem model24_at286 : AssociativeTheory286 (Fin 6) :=
  ⟨model24_eq307, model24_eq4343, model24_eq4512⟩

theorem model24_at287 : AssociativeTheory287 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4343, model24_eq4512⟩

theorem not_model24_at288 : Not (AssociativeTheory288 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at289 : Not (AssociativeTheory289 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at290 : AssociativeTheory290 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4343, model24_eq4512⟩

theorem not_model24_at291 : Not (AssociativeTheory291 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at292 : Not (AssociativeTheory292 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at293 : Not (AssociativeTheory293 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at294 : Not (AssociativeTheory294 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at295 : Not (AssociativeTheory295 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at296 : Not (AssociativeTheory296 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem model24_at297 : AssociativeTheory297 (Fin 6) :=
  ⟨model24_eq4293, model24_eq4343, model24_eq4512⟩

theorem not_model24_at298 : Not (AssociativeTheory298 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at299 : AssociativeTheory299 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4293, model24_eq4343, model24_eq4512⟩

theorem model24_at300 : AssociativeTheory300 (Fin 6) :=
  ⟨model24_eq4321, model24_eq4343, model24_eq4512⟩

theorem model24_at301 : AssociativeTheory301 (Fin 6) :=
  ⟨model24_eq307, model24_eq4321, model24_eq4343, model24_eq4512⟩

theorem model24_at302 : AssociativeTheory302 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4321, model24_eq4343, model24_eq4512⟩

theorem model24_at303 : AssociativeTheory303 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4321, model24_eq4343, model24_eq4512⟩

theorem model24_at304 : AssociativeTheory304 (Fin 6) :=
  ⟨model24_eq4293, model24_eq4321, model24_eq4343, model24_eq4512⟩

theorem model24_at305 : AssociativeTheory305 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4293, model24_eq4321, model24_eq4343, model24_eq4512⟩

theorem not_model24_at306 : Not (AssociativeTheory306 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at307 : Not (AssociativeTheory307 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3

theorem not_model24_at308 : Not (AssociativeTheory308 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at309 : Not (AssociativeTheory309 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at310 : Not (AssociativeTheory310 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq47

theorem not_model24_at311 : Not (AssociativeTheory311 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at312 : Not (AssociativeTheory312 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at313 : Not (AssociativeTheory313 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at314 : Not (AssociativeTheory314 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at315 : Not (AssociativeTheory315 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at316 : Not (AssociativeTheory316 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq411

theorem not_model24_at317 : Not (AssociativeTheory317 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at318 : Not (AssociativeTheory318 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at319 : Not (AssociativeTheory319 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at320 : Not (AssociativeTheory320 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at321 : Not (AssociativeTheory321 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at322 : Not (AssociativeTheory322 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3319

theorem not_model24_at323 : Not (AssociativeTheory323 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at324 : Not (AssociativeTheory324 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at325 : Not (AssociativeTheory325 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at326 : Not (AssociativeTheory326 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at327 : Not (AssociativeTheory327 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at328 : Not (AssociativeTheory328 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at329 : Not (AssociativeTheory329 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at330 : Not (AssociativeTheory330 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at331 : Not (AssociativeTheory331 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at332 : Not (AssociativeTheory332 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at333 : Not (AssociativeTheory333 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at334 : Not (AssociativeTheory334 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at335 : Not (AssociativeTheory335 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at336 : Not (AssociativeTheory336 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at337 : Not (AssociativeTheory337 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at338 : Not (AssociativeTheory338 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at339 : Not (AssociativeTheory339 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at340 : Not (AssociativeTheory340 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at341 : Not (AssociativeTheory341 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at342 : Not (AssociativeTheory342 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at343 : Not (AssociativeTheory343 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at344 : Not (AssociativeTheory344 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at345 : Not (AssociativeTheory345 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at346 : Not (AssociativeTheory346 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at347 : Not (AssociativeTheory347 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at348 : Not (AssociativeTheory348 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at349 : Not (AssociativeTheory349 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at350 : Not (AssociativeTheory350 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at351 : Not (AssociativeTheory351 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at352 : Not (AssociativeTheory352 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3

theorem not_model24_at353 : Not (AssociativeTheory353 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq8

theorem not_model24_at354 : Not (AssociativeTheory354 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at355 : Not (AssociativeTheory355 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq47

theorem not_model24_at356 : Not (AssociativeTheory356 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at357 : Not (AssociativeTheory357 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at358 : Not (AssociativeTheory358 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem not_model24_at359 : Not (AssociativeTheory359 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq323

theorem not_model24_at360 : Not (AssociativeTheory360 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq326

theorem not_model24_at361 : Not (AssociativeTheory361 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq411

theorem not_model24_at362 : Not (AssociativeTheory362 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at363 : Not (AssociativeTheory363 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at364 : Not (AssociativeTheory364 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at365 : Not (AssociativeTheory365 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at366 : Not (AssociativeTheory366 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3306

theorem not_model24_at367 : Not (AssociativeTheory367 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq3319

theorem not_model24_at368 : Not (AssociativeTheory368 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at369 : Not (AssociativeTheory369 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at370 : Not (AssociativeTheory370 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at371 : Not (AssociativeTheory371 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at372 : Not (AssociativeTheory372 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at373 : Not (AssociativeTheory373 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at374 : Not (AssociativeTheory374 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at375 : Not (AssociativeTheory375 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at376 : Not (AssociativeTheory376 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at377 : Not (AssociativeTheory377 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at378 : Not (AssociativeTheory378 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at379 : Not (AssociativeTheory379 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at380 : Not (AssociativeTheory380 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at381 : Not (AssociativeTheory381 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at382 : Not (AssociativeTheory382 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at383 : Not (AssociativeTheory383 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at384 : Not (AssociativeTheory384 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at385 : Not (AssociativeTheory385 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at386 : Not (AssociativeTheory386 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at387 : Not (AssociativeTheory387 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at388 : Not (AssociativeTheory388 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at389 : Not (AssociativeTheory389 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4362

theorem not_model24_at390 : Not (AssociativeTheory390 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at391 : Not (AssociativeTheory391 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at392 : Not (AssociativeTheory392 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at393 : Not (AssociativeTheory393 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at394 : Not (AssociativeTheory394 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at395 : Not (AssociativeTheory395 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4314

theorem not_model24_at396 : Not (AssociativeTheory396 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at397 : Not (AssociativeTheory397 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at398 : Not (AssociativeTheory398 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at399 : Not (AssociativeTheory399 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at400 : Not (AssociativeTheory400 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at401 : Not (AssociativeTheory401 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at402 : Not (AssociativeTheory402 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at403 : Not (AssociativeTheory403 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at404 : Not (AssociativeTheory404 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at405 : Not (AssociativeTheory405 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at406 : Not (AssociativeTheory406 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at407 : Not (AssociativeTheory407 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4358

theorem not_model24_at408 : Not (AssociativeTheory408 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at409 : Not (AssociativeTheory409 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at410 : Not (AssociativeTheory410 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at411 : Not (AssociativeTheory411 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at412 : Not (AssociativeTheory412 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at413 : Not (AssociativeTheory413 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at414 : Not (AssociativeTheory414 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at415 : Not (AssociativeTheory415 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at416 : Not (AssociativeTheory416 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at417 : Not (AssociativeTheory417 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at418 : Not (AssociativeTheory418 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem not_model24_at419 : Not (AssociativeTheory419 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4364

theorem model24_at420 : AssociativeTheory420 (Fin 6) :=
  ⟨model24_eq4369, model24_eq4512⟩

theorem model24_at421 : AssociativeTheory421 (Fin 6) :=
  ⟨model24_eq40, model24_eq4369, model24_eq4512⟩

theorem model24_at422 : AssociativeTheory422 (Fin 6) :=
  ⟨model24_eq307, model24_eq4369, model24_eq4512⟩

theorem model24_at423 : AssociativeTheory423 (Fin 6) :=
  ⟨model24_eq40, model24_eq307, model24_eq4369, model24_eq4512⟩

theorem not_model24_at424 : Not (AssociativeTheory424 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem model24_at425 : AssociativeTheory425 (Fin 6) :=
  ⟨model24_eq3253, model24_eq4369, model24_eq4512⟩

theorem model24_at426 : AssociativeTheory426 (Fin 6) :=
  ⟨model24_eq3267, model24_eq4369, model24_eq4512⟩

theorem not_model24_at427 : Not (AssociativeTheory427 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq309

theorem model24_at428 : AssociativeTheory428 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4369, model24_eq4512⟩

theorem not_model24_at429 : Not (AssociativeTheory429 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem not_model24_at430 : Not (AssociativeTheory430 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at431 : AssociativeTheory431 (Fin 6) :=
  ⟨model24_eq4270, model24_eq4369, model24_eq4512⟩

theorem not_model24_at432 : Not (AssociativeTheory432 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at433 : Not (AssociativeTheory433 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem not_model24_at434 : Not (AssociativeTheory434 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4273

theorem model24_at435 : AssociativeTheory435 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4369, model24_eq4512⟩

theorem not_model24_at436 : Not (AssociativeTheory436 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at437 : Not (AssociativeTheory437 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at438 : Not (AssociativeTheory438 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at439 : Not (AssociativeTheory439 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem model24_at440 : AssociativeTheory440 (Fin 6) :=
  ⟨model24_eq4284, model24_eq4369, model24_eq4512⟩

theorem model24_at441 : AssociativeTheory441 (Fin 6) :=
  ⟨model24_eq307, model24_eq4284, model24_eq4369, model24_eq4512⟩

theorem not_model24_at442 : Not (AssociativeTheory442 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4269

theorem model24_at443 : AssociativeTheory443 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4284, model24_eq4369, model24_eq4512⟩

theorem not_model24_at444 : Not (AssociativeTheory444 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at445 : Not (AssociativeTheory445 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at446 : Not (AssociativeTheory446 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4283

theorem not_model24_at447 : Not (AssociativeTheory447 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem not_model24_at448 : Not (AssociativeTheory448 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model24_eq4291

theorem model24_at449 : AssociativeTheory449 (Fin 6) :=
  ⟨model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at450 : AssociativeTheory450 (Fin 6) :=
  ⟨model24_eq40, model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at451 : AssociativeTheory451 (Fin 6) :=
  ⟨model24_eq307, model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at452 : AssociativeTheory452 (Fin 6) :=
  ⟨model24_eq3267, model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at453 : AssociativeTheory453 (Fin 6) :=
  ⟨model24_eq4268, model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at454 : AssociativeTheory454 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at455 : AssociativeTheory455 (Fin 6) :=
  ⟨model24_eq4284, model24_eq4321, model24_eq4369, model24_eq4512⟩

theorem model24_at456 : AssociativeTheory456 (Fin 6) :=
  ⟨model24_eq4276, model24_eq4284, model24_eq4321, model24_eq4369, model24_eq4512⟩
