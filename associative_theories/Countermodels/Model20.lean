import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model20_op := finOpTable "[[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,1,0],[0,2,0,5,0,0],[0,0,0,0,2,0]]"
private def model20 : Magma (Fin 6) where op := model20_op
private instance : Magma (Fin 6) := model20

private theorem model20_eq1 : Equation1 (Fin 6) := by decideFin!
private theorem model20_eq40 : Equation40 (Fin 6) := by decideFin!
private theorem model20_eq307 : Equation307 (Fin 6) := by decideFin!
private theorem model20_eq308 : Equation308 (Fin 6) := by decideFin!
private theorem model20_eq310 : Equation310 (Fin 6) := by decideFin!
private theorem model20_eq312 : Equation312 (Fin 6) := by decideFin!
private theorem model20_eq315 : Equation315 (Fin 6) := by decideFin!
private theorem model20_eq316 : Equation316 (Fin 6) := by decideFin!
private theorem model20_eq3253 : Equation3253 (Fin 6) := by decideFin!
private theorem model20_eq3255 : Equation3255 (Fin 6) := by decideFin!
private theorem model20_eq3256 : Equation3256 (Fin 6) := by decideFin!
private theorem model20_eq3258 : Equation3258 (Fin 6) := by decideFin!
private theorem model20_eq3259 : Equation3259 (Fin 6) := by decideFin!
private theorem model20_eq3260 : Equation3260 (Fin 6) := by decideFin!
private theorem model20_eq3261 : Equation3261 (Fin 6) := by decideFin!
private theorem model20_eq3264 : Equation3264 (Fin 6) := by decideFin!
private theorem model20_eq3265 : Equation3265 (Fin 6) := by decideFin!
private theorem model20_eq3267 : Equation3267 (Fin 6) := by decideFin!
private theorem model20_eq3271 : Equation3271 (Fin 6) := by decideFin!
private theorem model20_eq3273 : Equation3273 (Fin 6) := by decideFin!
private theorem model20_eq3274 : Equation3274 (Fin 6) := by decideFin!
private theorem model20_eq3275 : Equation3275 (Fin 6) := by decideFin!
private theorem model20_eq3277 : Equation3277 (Fin 6) := by decideFin!
private theorem model20_eq3278 : Equation3278 (Fin 6) := by decideFin!
private theorem model20_eq3290 : Equation3290 (Fin 6) := by decideFin!
private theorem model20_eq3292 : Equation3292 (Fin 6) := by decideFin!
private theorem model20_eq3300 : Equation3300 (Fin 6) := by decideFin!
private theorem model20_eq4268 : Equation4268 (Fin 6) := by decideFin!
private theorem model20_eq4270 : Equation4270 (Fin 6) := by decideFin!
private theorem model20_eq4272 : Equation4272 (Fin 6) := by decideFin!
private theorem model20_eq4275 : Equation4275 (Fin 6) := by decideFin!
private theorem model20_eq4276 : Equation4276 (Fin 6) := by decideFin!
private theorem model20_eq4277 : Equation4277 (Fin 6) := by decideFin!
private theorem model20_eq4280 : Equation4280 (Fin 6) := by decideFin!
private theorem model20_eq4284 : Equation4284 (Fin 6) := by decideFin!
private theorem model20_eq4288 : Equation4288 (Fin 6) := by decideFin!
private theorem model20_eq4290 : Equation4290 (Fin 6) := by decideFin!
private theorem model20_eq4293 : Equation4293 (Fin 6) := by decideFin!
private theorem model20_eq4297 : Equation4297 (Fin 6) := by decideFin!
private theorem model20_eq4299 : Equation4299 (Fin 6) := by decideFin!
private theorem model20_eq4304 : Equation4304 (Fin 6) := by decideFin!
private theorem model20_eq4343 : Equation4343 (Fin 6) := by decideFin!
private theorem model20_eq4369 : Equation4369 (Fin 6) := by decideFin!
private theorem model20_eq4512 : Equation4512 (Fin 6) := by decideFin!
private theorem not_model20_eq2 : Not (Equation2 (Fin 6)) := by decideFin!
private theorem not_model20_eq3 : Not (Equation3 (Fin 6)) := by decideFin!
private theorem not_model20_eq4 : Not (Equation4 (Fin 6)) := by decideFin!
private theorem not_model20_eq5 : Not (Equation5 (Fin 6)) := by decideFin!
private theorem not_model20_eq8 : Not (Equation8 (Fin 6)) := by decideFin!
private theorem not_model20_eq10 : Not (Equation10 (Fin 6)) := by decideFin!
private theorem not_model20_eq11 : Not (Equation11 (Fin 6)) := by decideFin!
private theorem not_model20_eq14 : Not (Equation14 (Fin 6)) := by decideFin!
private theorem not_model20_eq16 : Not (Equation16 (Fin 6)) := by decideFin!
private theorem not_model20_eq38 : Not (Equation38 (Fin 6)) := by decideFin!
private theorem not_model20_eq39 : Not (Equation39 (Fin 6)) := by decideFin!
private theorem not_model20_eq41 : Not (Equation41 (Fin 6)) := by decideFin!
private theorem not_model20_eq43 : Not (Equation43 (Fin 6)) := by decideFin!
private theorem not_model20_eq47 : Not (Equation47 (Fin 6)) := by decideFin!
private theorem not_model20_eq56 : Not (Equation56 (Fin 6)) := by decideFin!
private theorem not_model20_eq66 : Not (Equation66 (Fin 6)) := by decideFin!
private theorem not_model20_eq75 : Not (Equation75 (Fin 6)) := by decideFin!
private theorem not_model20_eq309 : Not (Equation309 (Fin 6)) := by decideFin!
private theorem not_model20_eq311 : Not (Equation311 (Fin 6)) := by decideFin!
private theorem not_model20_eq313 : Not (Equation313 (Fin 6)) := by decideFin!
private theorem not_model20_eq314 : Not (Equation314 (Fin 6)) := by decideFin!
private theorem not_model20_eq318 : Not (Equation318 (Fin 6)) := by decideFin!
private theorem not_model20_eq323 : Not (Equation323 (Fin 6)) := by decideFin!
private theorem not_model20_eq325 : Not (Equation325 (Fin 6)) := by decideFin!
private theorem not_model20_eq326 : Not (Equation326 (Fin 6)) := by decideFin!
private theorem not_model20_eq327 : Not (Equation327 (Fin 6)) := by decideFin!
private theorem not_model20_eq329 : Not (Equation329 (Fin 6)) := by decideFin!
private theorem not_model20_eq332 : Not (Equation332 (Fin 6)) := by decideFin!
private theorem not_model20_eq333 : Not (Equation333 (Fin 6)) := by decideFin!
private theorem not_model20_eq343 : Not (Equation343 (Fin 6)) := by decideFin!
private theorem not_model20_eq411 : Not (Equation411 (Fin 6)) := by decideFin!
private theorem not_model20_eq419 : Not (Equation419 (Fin 6)) := by decideFin!
private theorem not_model20_eq429 : Not (Equation429 (Fin 6)) := by decideFin!
private theorem not_model20_eq440 : Not (Equation440 (Fin 6)) := by decideFin!
private theorem not_model20_eq477 : Not (Equation477 (Fin 6)) := by decideFin!
private theorem not_model20_eq504 : Not (Equation504 (Fin 6)) := by decideFin!
private theorem not_model20_eq513 : Not (Equation513 (Fin 6)) := by decideFin!
private theorem not_model20_eq3306 : Not (Equation3306 (Fin 6)) := by decideFin!
private theorem not_model20_eq3308 : Not (Equation3308 (Fin 6)) := by decideFin!
private theorem not_model20_eq3309 : Not (Equation3309 (Fin 6)) := by decideFin!
private theorem not_model20_eq3315 : Not (Equation3315 (Fin 6)) := by decideFin!
private theorem not_model20_eq3316 : Not (Equation3316 (Fin 6)) := by decideFin!
private theorem not_model20_eq3319 : Not (Equation3319 (Fin 6)) := by decideFin!
private theorem not_model20_eq3322 : Not (Equation3322 (Fin 6)) := by decideFin!
private theorem not_model20_eq3323 : Not (Equation3323 (Fin 6)) := by decideFin!
private theorem not_model20_eq3326 : Not (Equation3326 (Fin 6)) := by decideFin!
private theorem not_model20_eq3331 : Not (Equation3331 (Fin 6)) := by decideFin!
private theorem not_model20_eq3334 : Not (Equation3334 (Fin 6)) := by decideFin!
private theorem not_model20_eq3342 : Not (Equation3342 (Fin 6)) := by decideFin!
private theorem not_model20_eq3346 : Not (Equation3346 (Fin 6)) := by decideFin!
private theorem not_model20_eq3350 : Not (Equation3350 (Fin 6)) := by decideFin!
private theorem not_model20_eq3353 : Not (Equation3353 (Fin 6)) := by decideFin!
private theorem not_model20_eq3388 : Not (Equation3388 (Fin 6)) := by decideFin!
private theorem not_model20_eq3414 : Not (Equation3414 (Fin 6)) := by decideFin!
private theorem not_model20_eq4269 : Not (Equation4269 (Fin 6)) := by decideFin!
private theorem not_model20_eq4271 : Not (Equation4271 (Fin 6)) := by decideFin!
private theorem not_model20_eq4273 : Not (Equation4273 (Fin 6)) := by decideFin!
private theorem not_model20_eq4274 : Not (Equation4274 (Fin 6)) := by decideFin!
private theorem not_model20_eq4278 : Not (Equation4278 (Fin 6)) := by decideFin!
private theorem not_model20_eq4279 : Not (Equation4279 (Fin 6)) := by decideFin!
private theorem not_model20_eq4283 : Not (Equation4283 (Fin 6)) := by decideFin!
private theorem not_model20_eq4286 : Not (Equation4286 (Fin 6)) := by decideFin!
private theorem not_model20_eq4287 : Not (Equation4287 (Fin 6)) := by decideFin!
private theorem not_model20_eq4291 : Not (Equation4291 (Fin 6)) := by decideFin!
private theorem not_model20_eq4296 : Not (Equation4296 (Fin 6)) := by decideFin!
private theorem not_model20_eq4300 : Not (Equation4300 (Fin 6)) := by decideFin!
private theorem not_model20_eq4301 : Not (Equation4301 (Fin 6)) := by decideFin!
private theorem not_model20_eq4305 : Not (Equation4305 (Fin 6)) := by decideFin!
private theorem not_model20_eq4314 : Not (Equation4314 (Fin 6)) := by decideFin!
private theorem not_model20_eq4315 : Not (Equation4315 (Fin 6)) := by decideFin!
private theorem not_model20_eq4318 : Not (Equation4318 (Fin 6)) := by decideFin!
private theorem not_model20_eq4320 : Not (Equation4320 (Fin 6)) := by decideFin!
private theorem not_model20_eq4321 : Not (Equation4321 (Fin 6)) := by decideFin!
private theorem not_model20_eq4325 : Not (Equation4325 (Fin 6)) := by decideFin!
private theorem not_model20_eq4327 : Not (Equation4327 (Fin 6)) := by decideFin!
private theorem not_model20_eq4331 : Not (Equation4331 (Fin 6)) := by decideFin!
private theorem not_model20_eq4358 : Not (Equation4358 (Fin 6)) := by decideFin!
private theorem not_model20_eq4362 : Not (Equation4362 (Fin 6)) := by decideFin!
private theorem not_model20_eq4364 : Not (Equation4364 (Fin 6)) := by decideFin!

theorem model20_at1 : AssociativeTheory1 (Fin 6) :=
  model20_eq4512

theorem not_model20_at2 : Not (AssociativeTheory2 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq2

theorem not_model20_at3 : Not (AssociativeTheory3 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3

theorem not_model20_at4 : Not (AssociativeTheory4 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4

theorem not_model20_at5 : Not (AssociativeTheory5 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq5

theorem not_model20_at6 : Not (AssociativeTheory6 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at7 : Not (AssociativeTheory7 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq10

theorem not_model20_at8 : Not (AssociativeTheory8 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq11

theorem not_model20_at9 : Not (AssociativeTheory9 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq14

theorem not_model20_at10 : Not (AssociativeTheory10 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq16

theorem not_model20_at11 : Not (AssociativeTheory11 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq38

theorem not_model20_at12 : Not (AssociativeTheory12 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq39

theorem not_model20_at13 : Not (AssociativeTheory13 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq38

theorem model20_at14 : AssociativeTheory14 (Fin 6) :=
  ⟨model20_eq40, model20_eq4512⟩

theorem not_model20_at15 : Not (AssociativeTheory15 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at16 : Not (AssociativeTheory16 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3

theorem not_model20_at17 : Not (AssociativeTheory17 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at18 : Not (AssociativeTheory18 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at19 : Not (AssociativeTheory19 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq47

theorem not_model20_at20 : Not (AssociativeTheory20 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at21 : Not (AssociativeTheory21 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq56

theorem not_model20_at22 : Not (AssociativeTheory22 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at23 : Not (AssociativeTheory23 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq75

theorem not_model20_at24 : Not (AssociativeTheory24 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq56

theorem model20_at25 : AssociativeTheory25 (Fin 6) :=
  ⟨model20_eq307, model20_eq4512⟩

theorem model20_at26 : AssociativeTheory26 (Fin 6) :=
  ⟨model20_eq40, model20_eq307, model20_eq4512⟩

theorem not_model20_at27 : Not (AssociativeTheory27 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at28 : Not (AssociativeTheory28 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem model20_at29 : AssociativeTheory29 (Fin 6) :=
  ⟨model20_eq308, model20_eq4512⟩

theorem not_model20_at30 : Not (AssociativeTheory30 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem not_model20_at31 : Not (AssociativeTheory31 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem not_model20_at32 : Not (AssociativeTheory32 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem model20_at33 : AssociativeTheory33 (Fin 6) :=
  ⟨model20_eq310, model20_eq4512⟩

theorem not_model20_at34 : Not (AssociativeTheory34 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq311

theorem not_model20_at35 : Not (AssociativeTheory35 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq311

theorem not_model20_at36 : Not (AssociativeTheory36 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem model20_at37 : AssociativeTheory37 (Fin 6) :=
  ⟨model20_eq312, model20_eq4512⟩

theorem not_model20_at38 : Not (AssociativeTheory38 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem model20_at39 : AssociativeTheory39 (Fin 6) :=
  ⟨model20_eq315, model20_eq4512⟩

theorem not_model20_at40 : Not (AssociativeTheory40 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq318

theorem not_model20_at41 : Not (AssociativeTheory41 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at42 : Not (AssociativeTheory42 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at43 : Not (AssociativeTheory43 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem not_model20_at44 : Not (AssociativeTheory44 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at45 : Not (AssociativeTheory45 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq325

theorem not_model20_at46 : Not (AssociativeTheory46 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3

theorem not_model20_at47 : Not (AssociativeTheory47 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq325

theorem not_model20_at48 : Not (AssociativeTheory48 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at49 : Not (AssociativeTheory49 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at50 : Not (AssociativeTheory50 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at51 : Not (AssociativeTheory51 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq333

theorem not_model20_at52 : Not (AssociativeTheory52 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3

theorem not_model20_at53 : Not (AssociativeTheory53 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at54 : Not (AssociativeTheory54 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq411

theorem not_model20_at55 : Not (AssociativeTheory55 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at56 : Not (AssociativeTheory56 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq419

theorem not_model20_at57 : Not (AssociativeTheory57 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq429

theorem not_model20_at58 : Not (AssociativeTheory58 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq440

theorem not_model20_at59 : Not (AssociativeTheory59 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at60 : Not (AssociativeTheory60 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq504

theorem not_model20_at61 : Not (AssociativeTheory61 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq513

theorem not_model20_at62 : Not (AssociativeTheory62 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq440

theorem model20_at63 : AssociativeTheory63 (Fin 6) :=
  ⟨model20_eq3253, model20_eq4512⟩

theorem not_model20_at64 : Not (AssociativeTheory64 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem model20_at65 : AssociativeTheory65 (Fin 6) :=
  ⟨model20_eq3255, model20_eq4512⟩

theorem not_model20_at66 : Not (AssociativeTheory66 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem model20_at67 : AssociativeTheory67 (Fin 6) :=
  ⟨model20_eq3256, model20_eq4512⟩

theorem model20_at68 : AssociativeTheory68 (Fin 6) :=
  ⟨model20_eq3258, model20_eq4512⟩

theorem not_model20_at69 : Not (AssociativeTheory69 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem model20_at70 : AssociativeTheory70 (Fin 6) :=
  ⟨model20_eq3255, model20_eq3258, model20_eq4512⟩

theorem model20_at71 : AssociativeTheory71 (Fin 6) :=
  ⟨model20_eq3259, model20_eq4512⟩

theorem model20_at72 : AssociativeTheory72 (Fin 6) :=
  ⟨model20_eq3260, model20_eq4512⟩

theorem model20_at73 : AssociativeTheory73 (Fin 6) :=
  ⟨model20_eq40, model20_eq3260, model20_eq4512⟩

theorem model20_at74 : AssociativeTheory74 (Fin 6) :=
  ⟨model20_eq3261, model20_eq4512⟩

theorem model20_at75 : AssociativeTheory75 (Fin 6) :=
  ⟨model20_eq3264, model20_eq4512⟩

theorem model20_at76 : AssociativeTheory76 (Fin 6) :=
  ⟨model20_eq40, model20_eq3264, model20_eq4512⟩

theorem model20_at77 : AssociativeTheory77 (Fin 6) :=
  ⟨model20_eq308, model20_eq3264, model20_eq4512⟩

theorem model20_at78 : AssociativeTheory78 (Fin 6) :=
  ⟨model20_eq312, model20_eq3264, model20_eq4512⟩

theorem model20_at79 : AssociativeTheory79 (Fin 6) :=
  ⟨model20_eq3260, model20_eq3264, model20_eq4512⟩

theorem model20_at80 : AssociativeTheory80 (Fin 6) :=
  ⟨model20_eq40, model20_eq3260, model20_eq3264, model20_eq4512⟩

theorem model20_at81 : AssociativeTheory81 (Fin 6) :=
  ⟨model20_eq3265, model20_eq4512⟩

theorem model20_at82 : AssociativeTheory82 (Fin 6) :=
  ⟨model20_eq40, model20_eq3265, model20_eq4512⟩

theorem model20_at83 : AssociativeTheory83 (Fin 6) :=
  ⟨model20_eq3260, model20_eq3265, model20_eq4512⟩

theorem model20_at84 : AssociativeTheory84 (Fin 6) :=
  ⟨model20_eq40, model20_eq3260, model20_eq3265, model20_eq4512⟩

theorem model20_at85 : AssociativeTheory85 (Fin 6) :=
  ⟨model20_eq3264, model20_eq3265, model20_eq4512⟩

theorem model20_at86 : AssociativeTheory86 (Fin 6) :=
  ⟨model20_eq40, model20_eq3264, model20_eq3265, model20_eq4512⟩

theorem model20_at87 : AssociativeTheory87 (Fin 6) :=
  ⟨model20_eq3260, model20_eq3264, model20_eq3265, model20_eq4512⟩

theorem model20_at88 : AssociativeTheory88 (Fin 6) :=
  ⟨model20_eq40, model20_eq3260, model20_eq3264, model20_eq3265, model20_eq4512⟩

theorem model20_at89 : AssociativeTheory89 (Fin 6) :=
  ⟨model20_eq3267, model20_eq4512⟩

theorem model20_at90 : AssociativeTheory90 (Fin 6) :=
  ⟨model20_eq40, model20_eq3267, model20_eq4512⟩

theorem not_model20_at91 : Not (AssociativeTheory91 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at92 : Not (AssociativeTheory92 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem not_model20_at93 : Not (AssociativeTheory93 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem model20_at94 : AssociativeTheory94 (Fin 6) :=
  ⟨model20_eq3271, model20_eq4512⟩

theorem model20_at95 : AssociativeTheory95 (Fin 6) :=
  ⟨model20_eq3274, model20_eq4512⟩

theorem model20_at96 : AssociativeTheory96 (Fin 6) :=
  ⟨model20_eq3264, model20_eq3274, model20_eq4512⟩

theorem model20_at97 : AssociativeTheory97 (Fin 6) :=
  ⟨model20_eq3278, model20_eq4512⟩

theorem model20_at98 : AssociativeTheory98 (Fin 6) :=
  ⟨model20_eq3292, model20_eq4512⟩

theorem model20_at99 : AssociativeTheory99 (Fin 6) :=
  ⟨model20_eq3264, model20_eq3292, model20_eq4512⟩

theorem model20_at100 : AssociativeTheory100 (Fin 6) :=
  ⟨model20_eq3274, model20_eq3292, model20_eq4512⟩

theorem model20_at101 : AssociativeTheory101 (Fin 6) :=
  ⟨model20_eq3264, model20_eq3274, model20_eq3292, model20_eq4512⟩

theorem model20_at102 : AssociativeTheory102 (Fin 6) :=
  ⟨model20_eq3300, model20_eq4512⟩

theorem not_model20_at103 : Not (AssociativeTheory103 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem not_model20_at104 : Not (AssociativeTheory104 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at105 : Not (AssociativeTheory105 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at106 : Not (AssociativeTheory106 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at107 : Not (AssociativeTheory107 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at108 : Not (AssociativeTheory108 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at109 : Not (AssociativeTheory109 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at110 : Not (AssociativeTheory110 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at111 : Not (AssociativeTheory111 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3308

theorem not_model20_at112 : Not (AssociativeTheory112 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at113 : Not (AssociativeTheory113 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3315

theorem not_model20_at114 : Not (AssociativeTheory114 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at115 : Not (AssociativeTheory115 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3315

theorem not_model20_at116 : Not (AssociativeTheory116 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at117 : Not (AssociativeTheory117 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3316

theorem not_model20_at118 : Not (AssociativeTheory118 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at119 : Not (AssociativeTheory119 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at120 : Not (AssociativeTheory120 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3319

theorem not_model20_at121 : Not (AssociativeTheory121 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at122 : Not (AssociativeTheory122 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3346

theorem not_model20_at123 : Not (AssociativeTheory123 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at124 : Not (AssociativeTheory124 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3353

theorem not_model20_at125 : Not (AssociativeTheory125 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at126 : Not (AssociativeTheory126 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3319

theorem model20_at127 : AssociativeTheory127 (Fin 6) :=
  ⟨model20_eq4268, model20_eq4512⟩

theorem not_model20_at128 : Not (AssociativeTheory128 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at129 : Not (AssociativeTheory129 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at130 : Not (AssociativeTheory130 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at131 : AssociativeTheory131 (Fin 6) :=
  ⟨model20_eq4270, model20_eq4512⟩

theorem not_model20_at132 : Not (AssociativeTheory132 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem model20_at133 : AssociativeTheory133 (Fin 6) :=
  ⟨model20_eq4268, model20_eq4270, model20_eq4512⟩

theorem not_model20_at134 : Not (AssociativeTheory134 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at135 : Not (AssociativeTheory135 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at136 : Not (AssociativeTheory136 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4271

theorem not_model20_at137 : Not (AssociativeTheory137 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem model20_at138 : AssociativeTheory138 (Fin 6) :=
  ⟨model20_eq4272, model20_eq4512⟩

theorem model20_at139 : AssociativeTheory139 (Fin 6) :=
  ⟨model20_eq4268, model20_eq4272, model20_eq4512⟩

theorem not_model20_at140 : Not (AssociativeTheory140 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at141 : Not (AssociativeTheory141 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at142 : AssociativeTheory142 (Fin 6) :=
  ⟨model20_eq4270, model20_eq4272, model20_eq4512⟩

theorem not_model20_at143 : Not (AssociativeTheory143 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at144 : Not (AssociativeTheory144 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4271

theorem not_model20_at145 : Not (AssociativeTheory145 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at146 : Not (AssociativeTheory146 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at147 : Not (AssociativeTheory147 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at148 : Not (AssociativeTheory148 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at149 : Not (AssociativeTheory149 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem model20_at150 : AssociativeTheory150 (Fin 6) :=
  ⟨model20_eq4275, model20_eq4512⟩

theorem model20_at151 : AssociativeTheory151 (Fin 6) :=
  ⟨model20_eq4268, model20_eq4275, model20_eq4512⟩

theorem not_model20_at152 : Not (AssociativeTheory152 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at153 : AssociativeTheory153 (Fin 6) :=
  ⟨model20_eq4270, model20_eq4275, model20_eq4512⟩

theorem model20_at154 : AssociativeTheory154 (Fin 6) :=
  ⟨model20_eq4272, model20_eq4275, model20_eq4512⟩

theorem not_model20_at155 : Not (AssociativeTheory155 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at156 : Not (AssociativeTheory156 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at157 : Not (AssociativeTheory157 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem model20_at158 : AssociativeTheory158 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4512⟩

theorem not_model20_at159 : Not (AssociativeTheory159 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at160 : Not (AssociativeTheory160 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4278

theorem not_model20_at161 : Not (AssociativeTheory161 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at162 : Not (AssociativeTheory162 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq47

theorem not_model20_at163 : Not (AssociativeTheory163 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq56

theorem not_model20_at164 : Not (AssociativeTheory164 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at165 : Not (AssociativeTheory165 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at166 : Not (AssociativeTheory166 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq411

theorem not_model20_at167 : Not (AssociativeTheory167 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq440

theorem not_model20_at168 : Not (AssociativeTheory168 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at169 : Not (AssociativeTheory169 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at170 : Not (AssociativeTheory170 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3319

theorem not_model20_at171 : Not (AssociativeTheory171 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at172 : Not (AssociativeTheory172 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at173 : Not (AssociativeTheory173 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem model20_at174 : AssociativeTheory174 (Fin 6) :=
  ⟨model20_eq4284, model20_eq4512⟩

theorem not_model20_at175 : Not (AssociativeTheory175 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem model20_at176 : AssociativeTheory176 (Fin 6) :=
  ⟨model20_eq307, model20_eq4284, model20_eq4512⟩

theorem not_model20_at177 : Not (AssociativeTheory177 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at178 : Not (AssociativeTheory178 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at179 : Not (AssociativeTheory179 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem model20_at180 : AssociativeTheory180 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4284, model20_eq4512⟩

theorem not_model20_at181 : Not (AssociativeTheory181 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq43

theorem not_model20_at182 : Not (AssociativeTheory182 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at183 : Not (AssociativeTheory183 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at184 : Not (AssociativeTheory184 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at185 : Not (AssociativeTheory185 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4287

theorem not_model20_at186 : Not (AssociativeTheory186 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4287

theorem model20_at187 : AssociativeTheory187 (Fin 6) :=
  ⟨model20_eq4290, model20_eq4512⟩

theorem model20_at188 : AssociativeTheory188 (Fin 6) :=
  ⟨model20_eq307, model20_eq4290, model20_eq4512⟩

theorem not_model20_at189 : Not (AssociativeTheory189 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq411

theorem model20_at190 : AssociativeTheory190 (Fin 6) :=
  ⟨model20_eq3253, model20_eq4290, model20_eq4512⟩

theorem not_model20_at191 : Not (AssociativeTheory191 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at192 : Not (AssociativeTheory192 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem model20_at193 : AssociativeTheory193 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4290, model20_eq4512⟩

theorem not_model20_at194 : Not (AssociativeTheory194 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at195 : Not (AssociativeTheory195 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at196 : Not (AssociativeTheory196 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at197 : Not (AssociativeTheory197 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem model20_at198 : AssociativeTheory198 (Fin 6) :=
  ⟨model20_eq4284, model20_eq4290, model20_eq4512⟩

theorem model20_at199 : AssociativeTheory199 (Fin 6) :=
  ⟨model20_eq307, model20_eq4284, model20_eq4290, model20_eq4512⟩

theorem not_model20_at200 : Not (AssociativeTheory200 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at201 : AssociativeTheory201 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4284, model20_eq4290, model20_eq4512⟩

theorem not_model20_at202 : Not (AssociativeTheory202 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at203 : Not (AssociativeTheory203 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at204 : Not (AssociativeTheory204 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at205 : Not (AssociativeTheory205 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at206 : Not (AssociativeTheory206 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at207 : Not (AssociativeTheory207 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at208 : Not (AssociativeTheory208 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at209 : Not (AssociativeTheory209 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at210 : Not (AssociativeTheory210 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at211 : Not (AssociativeTheory211 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at212 : Not (AssociativeTheory212 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at213 : Not (AssociativeTheory213 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at214 : Not (AssociativeTheory214 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at215 : Not (AssociativeTheory215 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at216 : Not (AssociativeTheory216 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at217 : Not (AssociativeTheory217 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at218 : Not (AssociativeTheory218 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at219 : Not (AssociativeTheory219 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at220 : Not (AssociativeTheory220 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at221 : Not (AssociativeTheory221 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem model20_at222 : AssociativeTheory222 (Fin 6) :=
  ⟨model20_eq4293, model20_eq4512⟩

theorem model20_at223 : AssociativeTheory223 (Fin 6) :=
  ⟨model20_eq307, model20_eq4293, model20_eq4512⟩

theorem not_model20_at224 : Not (AssociativeTheory224 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at225 : AssociativeTheory225 (Fin 6) :=
  ⟨model20_eq4270, model20_eq4293, model20_eq4512⟩

theorem not_model20_at226 : Not (AssociativeTheory226 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at227 : AssociativeTheory227 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4293, model20_eq4512⟩

theorem not_model20_at228 : Not (AssociativeTheory228 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4300

theorem not_model20_at229 : Not (AssociativeTheory229 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4300

theorem not_model20_at230 : Not (AssociativeTheory230 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at231 : Not (AssociativeTheory231 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at232 : Not (AssociativeTheory232 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at233 : Not (AssociativeTheory233 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at234 : Not (AssociativeTheory234 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at235 : Not (AssociativeTheory235 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at236 : Not (AssociativeTheory236 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at237 : Not (AssociativeTheory237 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at238 : Not (AssociativeTheory238 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at239 : Not (AssociativeTheory239 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4315

theorem not_model20_at240 : Not (AssociativeTheory240 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4315

theorem not_model20_at241 : Not (AssociativeTheory241 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at242 : Not (AssociativeTheory242 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq47

theorem not_model20_at243 : Not (AssociativeTheory243 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq75

theorem not_model20_at244 : Not (AssociativeTheory244 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at245 : Not (AssociativeTheory245 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at246 : Not (AssociativeTheory246 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq411

theorem not_model20_at247 : Not (AssociativeTheory247 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq513

theorem not_model20_at248 : Not (AssociativeTheory248 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at249 : Not (AssociativeTheory249 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at250 : Not (AssociativeTheory250 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at251 : Not (AssociativeTheory251 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at252 : Not (AssociativeTheory252 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at253 : Not (AssociativeTheory253 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at254 : Not (AssociativeTheory254 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at255 : Not (AssociativeTheory255 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4320

theorem not_model20_at256 : Not (AssociativeTheory256 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at257 : Not (AssociativeTheory257 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at258 : Not (AssociativeTheory258 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at259 : Not (AssociativeTheory259 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at260 : Not (AssociativeTheory260 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at261 : Not (AssociativeTheory261 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at262 : Not (AssociativeTheory262 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at263 : Not (AssociativeTheory263 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at264 : Not (AssociativeTheory264 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at265 : Not (AssociativeTheory265 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at266 : Not (AssociativeTheory266 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at267 : Not (AssociativeTheory267 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at268 : Not (AssociativeTheory268 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at269 : Not (AssociativeTheory269 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at270 : Not (AssociativeTheory270 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at271 : Not (AssociativeTheory271 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at272 : Not (AssociativeTheory272 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at273 : Not (AssociativeTheory273 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at274 : Not (AssociativeTheory274 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at275 : Not (AssociativeTheory275 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at276 : Not (AssociativeTheory276 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at277 : Not (AssociativeTheory277 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at278 : Not (AssociativeTheory278 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at279 : Not (AssociativeTheory279 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at280 : Not (AssociativeTheory280 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at281 : Not (AssociativeTheory281 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at282 : Not (AssociativeTheory282 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at283 : Not (AssociativeTheory283 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at284 : Not (AssociativeTheory284 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem model20_at285 : AssociativeTheory285 (Fin 6) :=
  ⟨model20_eq4343, model20_eq4512⟩

theorem model20_at286 : AssociativeTheory286 (Fin 6) :=
  ⟨model20_eq307, model20_eq4343, model20_eq4512⟩

theorem model20_at287 : AssociativeTheory287 (Fin 6) :=
  ⟨model20_eq4268, model20_eq4343, model20_eq4512⟩

theorem not_model20_at288 : Not (AssociativeTheory288 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at289 : Not (AssociativeTheory289 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at290 : AssociativeTheory290 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4343, model20_eq4512⟩

theorem not_model20_at291 : Not (AssociativeTheory291 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at292 : Not (AssociativeTheory292 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at293 : Not (AssociativeTheory293 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at294 : Not (AssociativeTheory294 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at295 : Not (AssociativeTheory295 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at296 : Not (AssociativeTheory296 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem model20_at297 : AssociativeTheory297 (Fin 6) :=
  ⟨model20_eq4293, model20_eq4343, model20_eq4512⟩

theorem not_model20_at298 : Not (AssociativeTheory298 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at299 : AssociativeTheory299 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4293, model20_eq4343, model20_eq4512⟩

theorem not_model20_at300 : Not (AssociativeTheory300 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at301 : Not (AssociativeTheory301 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at302 : Not (AssociativeTheory302 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at303 : Not (AssociativeTheory303 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at304 : Not (AssociativeTheory304 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at305 : Not (AssociativeTheory305 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at306 : Not (AssociativeTheory306 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at307 : Not (AssociativeTheory307 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3

theorem not_model20_at308 : Not (AssociativeTheory308 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at309 : Not (AssociativeTheory309 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at310 : Not (AssociativeTheory310 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq47

theorem not_model20_at311 : Not (AssociativeTheory311 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at312 : Not (AssociativeTheory312 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at313 : Not (AssociativeTheory313 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at314 : Not (AssociativeTheory314 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at315 : Not (AssociativeTheory315 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at316 : Not (AssociativeTheory316 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq411

theorem not_model20_at317 : Not (AssociativeTheory317 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at318 : Not (AssociativeTheory318 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at319 : Not (AssociativeTheory319 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at320 : Not (AssociativeTheory320 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at321 : Not (AssociativeTheory321 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at322 : Not (AssociativeTheory322 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3319

theorem not_model20_at323 : Not (AssociativeTheory323 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at324 : Not (AssociativeTheory324 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at325 : Not (AssociativeTheory325 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at326 : Not (AssociativeTheory326 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at327 : Not (AssociativeTheory327 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at328 : Not (AssociativeTheory328 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at329 : Not (AssociativeTheory329 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at330 : Not (AssociativeTheory330 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at331 : Not (AssociativeTheory331 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at332 : Not (AssociativeTheory332 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at333 : Not (AssociativeTheory333 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at334 : Not (AssociativeTheory334 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at335 : Not (AssociativeTheory335 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at336 : Not (AssociativeTheory336 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at337 : Not (AssociativeTheory337 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at338 : Not (AssociativeTheory338 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at339 : Not (AssociativeTheory339 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at340 : Not (AssociativeTheory340 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at341 : Not (AssociativeTheory341 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at342 : Not (AssociativeTheory342 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at343 : Not (AssociativeTheory343 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at344 : Not (AssociativeTheory344 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at345 : Not (AssociativeTheory345 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at346 : Not (AssociativeTheory346 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at347 : Not (AssociativeTheory347 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at348 : Not (AssociativeTheory348 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at349 : Not (AssociativeTheory349 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at350 : Not (AssociativeTheory350 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at351 : Not (AssociativeTheory351 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at352 : Not (AssociativeTheory352 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3

theorem not_model20_at353 : Not (AssociativeTheory353 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq8

theorem not_model20_at354 : Not (AssociativeTheory354 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at355 : Not (AssociativeTheory355 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq47

theorem not_model20_at356 : Not (AssociativeTheory356 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at357 : Not (AssociativeTheory357 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at358 : Not (AssociativeTheory358 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem not_model20_at359 : Not (AssociativeTheory359 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq323

theorem not_model20_at360 : Not (AssociativeTheory360 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq326

theorem not_model20_at361 : Not (AssociativeTheory361 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq411

theorem not_model20_at362 : Not (AssociativeTheory362 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at363 : Not (AssociativeTheory363 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at364 : Not (AssociativeTheory364 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at365 : Not (AssociativeTheory365 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at366 : Not (AssociativeTheory366 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3306

theorem not_model20_at367 : Not (AssociativeTheory367 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq3319

theorem not_model20_at368 : Not (AssociativeTheory368 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at369 : Not (AssociativeTheory369 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at370 : Not (AssociativeTheory370 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at371 : Not (AssociativeTheory371 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at372 : Not (AssociativeTheory372 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at373 : Not (AssociativeTheory373 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at374 : Not (AssociativeTheory374 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at375 : Not (AssociativeTheory375 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at376 : Not (AssociativeTheory376 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at377 : Not (AssociativeTheory377 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at378 : Not (AssociativeTheory378 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at379 : Not (AssociativeTheory379 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at380 : Not (AssociativeTheory380 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at381 : Not (AssociativeTheory381 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at382 : Not (AssociativeTheory382 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at383 : Not (AssociativeTheory383 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at384 : Not (AssociativeTheory384 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at385 : Not (AssociativeTheory385 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at386 : Not (AssociativeTheory386 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at387 : Not (AssociativeTheory387 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at388 : Not (AssociativeTheory388 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at389 : Not (AssociativeTheory389 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4362

theorem not_model20_at390 : Not (AssociativeTheory390 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at391 : Not (AssociativeTheory391 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at392 : Not (AssociativeTheory392 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at393 : Not (AssociativeTheory393 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at394 : Not (AssociativeTheory394 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at395 : Not (AssociativeTheory395 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4314

theorem not_model20_at396 : Not (AssociativeTheory396 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at397 : Not (AssociativeTheory397 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at398 : Not (AssociativeTheory398 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at399 : Not (AssociativeTheory399 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at400 : Not (AssociativeTheory400 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at401 : Not (AssociativeTheory401 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at402 : Not (AssociativeTheory402 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at403 : Not (AssociativeTheory403 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at404 : Not (AssociativeTheory404 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at405 : Not (AssociativeTheory405 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at406 : Not (AssociativeTheory406 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at407 : Not (AssociativeTheory407 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4358

theorem not_model20_at408 : Not (AssociativeTheory408 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at409 : Not (AssociativeTheory409 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at410 : Not (AssociativeTheory410 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at411 : Not (AssociativeTheory411 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at412 : Not (AssociativeTheory412 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at413 : Not (AssociativeTheory413 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at414 : Not (AssociativeTheory414 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at415 : Not (AssociativeTheory415 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at416 : Not (AssociativeTheory416 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at417 : Not (AssociativeTheory417 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at418 : Not (AssociativeTheory418 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem not_model20_at419 : Not (AssociativeTheory419 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4364

theorem model20_at420 : AssociativeTheory420 (Fin 6) :=
  ⟨model20_eq4369, model20_eq4512⟩

theorem model20_at421 : AssociativeTheory421 (Fin 6) :=
  ⟨model20_eq40, model20_eq4369, model20_eq4512⟩

theorem model20_at422 : AssociativeTheory422 (Fin 6) :=
  ⟨model20_eq307, model20_eq4369, model20_eq4512⟩

theorem model20_at423 : AssociativeTheory423 (Fin 6) :=
  ⟨model20_eq40, model20_eq307, model20_eq4369, model20_eq4512⟩

theorem not_model20_at424 : Not (AssociativeTheory424 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem model20_at425 : AssociativeTheory425 (Fin 6) :=
  ⟨model20_eq3253, model20_eq4369, model20_eq4512⟩

theorem model20_at426 : AssociativeTheory426 (Fin 6) :=
  ⟨model20_eq3267, model20_eq4369, model20_eq4512⟩

theorem not_model20_at427 : Not (AssociativeTheory427 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq309

theorem model20_at428 : AssociativeTheory428 (Fin 6) :=
  ⟨model20_eq4268, model20_eq4369, model20_eq4512⟩

theorem not_model20_at429 : Not (AssociativeTheory429 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem not_model20_at430 : Not (AssociativeTheory430 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at431 : AssociativeTheory431 (Fin 6) :=
  ⟨model20_eq4270, model20_eq4369, model20_eq4512⟩

theorem not_model20_at432 : Not (AssociativeTheory432 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at433 : Not (AssociativeTheory433 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem not_model20_at434 : Not (AssociativeTheory434 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4273

theorem model20_at435 : AssociativeTheory435 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4369, model20_eq4512⟩

theorem not_model20_at436 : Not (AssociativeTheory436 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at437 : Not (AssociativeTheory437 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at438 : Not (AssociativeTheory438 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at439 : Not (AssociativeTheory439 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem model20_at440 : AssociativeTheory440 (Fin 6) :=
  ⟨model20_eq4284, model20_eq4369, model20_eq4512⟩

theorem model20_at441 : AssociativeTheory441 (Fin 6) :=
  ⟨model20_eq307, model20_eq4284, model20_eq4369, model20_eq4512⟩

theorem not_model20_at442 : Not (AssociativeTheory442 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4269

theorem model20_at443 : AssociativeTheory443 (Fin 6) :=
  ⟨model20_eq4276, model20_eq4284, model20_eq4369, model20_eq4512⟩

theorem not_model20_at444 : Not (AssociativeTheory444 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at445 : Not (AssociativeTheory445 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at446 : Not (AssociativeTheory446 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4283

theorem not_model20_at447 : Not (AssociativeTheory447 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at448 : Not (AssociativeTheory448 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4291

theorem not_model20_at449 : Not (AssociativeTheory449 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at450 : Not (AssociativeTheory450 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at451 : Not (AssociativeTheory451 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at452 : Not (AssociativeTheory452 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at453 : Not (AssociativeTheory453 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at454 : Not (AssociativeTheory454 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at455 : Not (AssociativeTheory455 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321

theorem not_model20_at456 : Not (AssociativeTheory456 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model20_eq4321
