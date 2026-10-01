import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model14_op := finOpTable "[[0,0,0,0],[0,0,3,0],[2,2,2,2],[3,3,3,3]]"
private def model14 : Magma (Fin 4) where op := model14_op
private instance : Magma (Fin 4) := model14

private theorem model14_eq1 : Equation1 (Fin 4) := by decideFin!
private theorem not_model14_eq2 : Not (Equation2 (Fin 4)) := by decideFin!
private theorem not_model14_eq3 : Not (Equation3 (Fin 4)) := by decideFin!
private theorem not_model14_eq4 : Not (Equation4 (Fin 4)) := by decideFin!
private theorem not_model14_eq5 : Not (Equation5 (Fin 4)) := by decideFin!
private theorem not_model14_eq8 : Not (Equation8 (Fin 4)) := by decideFin!
private theorem not_model14_eq10 : Not (Equation10 (Fin 4)) := by decideFin!
private theorem not_model14_eq11 : Not (Equation11 (Fin 4)) := by decideFin!
private theorem not_model14_eq14 : Not (Equation14 (Fin 4)) := by decideFin!
private theorem not_model14_eq16 : Not (Equation16 (Fin 4)) := by decideFin!
private theorem not_model14_eq38 : Not (Equation38 (Fin 4)) := by decideFin!
private theorem not_model14_eq39 : Not (Equation39 (Fin 4)) := by decideFin!
private theorem not_model14_eq40 : Not (Equation40 (Fin 4)) := by decideFin!
private theorem not_model14_eq41 : Not (Equation41 (Fin 4)) := by decideFin!
private theorem not_model14_eq43 : Not (Equation43 (Fin 4)) := by decideFin!
private theorem not_model14_eq47 : Not (Equation47 (Fin 4)) := by decideFin!
private theorem not_model14_eq56 : Not (Equation56 (Fin 4)) := by decideFin!
private theorem not_model14_eq66 : Not (Equation66 (Fin 4)) := by decideFin!
private theorem not_model14_eq75 : Not (Equation75 (Fin 4)) := by decideFin!
private theorem model14_eq307 : Equation307 (Fin 4) := by decideFin!
private theorem model14_eq308 : Equation308 (Fin 4) := by decideFin!
private theorem not_model14_eq309 : Not (Equation309 (Fin 4)) := by decideFin!
private theorem not_model14_eq310 : Not (Equation310 (Fin 4)) := by decideFin!
private theorem not_model14_eq311 : Not (Equation311 (Fin 4)) := by decideFin!
private theorem not_model14_eq312 : Not (Equation312 (Fin 4)) := by decideFin!
private theorem not_model14_eq313 : Not (Equation313 (Fin 4)) := by decideFin!
private theorem not_model14_eq314 : Not (Equation314 (Fin 4)) := by decideFin!
private theorem not_model14_eq315 : Not (Equation315 (Fin 4)) := by decideFin!
private theorem not_model14_eq316 : Not (Equation316 (Fin 4)) := by decideFin!
private theorem not_model14_eq318 : Not (Equation318 (Fin 4)) := by decideFin!
private theorem not_model14_eq323 : Not (Equation323 (Fin 4)) := by decideFin!
private theorem model14_eq325 : Equation325 (Fin 4) := by decideFin!
private theorem model14_eq326 : Equation326 (Fin 4) := by decideFin!
private theorem model14_eq327 : Equation327 (Fin 4) := by decideFin!
private theorem not_model14_eq329 : Not (Equation329 (Fin 4)) := by decideFin!
private theorem not_model14_eq332 : Not (Equation332 (Fin 4)) := by decideFin!
private theorem not_model14_eq333 : Not (Equation333 (Fin 4)) := by decideFin!
private theorem not_model14_eq343 : Not (Equation343 (Fin 4)) := by decideFin!
private theorem not_model14_eq411 : Not (Equation411 (Fin 4)) := by decideFin!
private theorem not_model14_eq419 : Not (Equation419 (Fin 4)) := by decideFin!
private theorem not_model14_eq429 : Not (Equation429 (Fin 4)) := by decideFin!
private theorem not_model14_eq440 : Not (Equation440 (Fin 4)) := by decideFin!
private theorem not_model14_eq477 : Not (Equation477 (Fin 4)) := by decideFin!
private theorem not_model14_eq504 : Not (Equation504 (Fin 4)) := by decideFin!
private theorem not_model14_eq513 : Not (Equation513 (Fin 4)) := by decideFin!
private theorem model14_eq3253 : Equation3253 (Fin 4) := by decideFin!
private theorem model14_eq3255 : Equation3255 (Fin 4) := by decideFin!
private theorem model14_eq3256 : Equation3256 (Fin 4) := by decideFin!
private theorem not_model14_eq3258 : Not (Equation3258 (Fin 4)) := by decideFin!
private theorem not_model14_eq3259 : Not (Equation3259 (Fin 4)) := by decideFin!
private theorem not_model14_eq3260 : Not (Equation3260 (Fin 4)) := by decideFin!
private theorem not_model14_eq3261 : Not (Equation3261 (Fin 4)) := by decideFin!
private theorem not_model14_eq3264 : Not (Equation3264 (Fin 4)) := by decideFin!
private theorem not_model14_eq3265 : Not (Equation3265 (Fin 4)) := by decideFin!
private theorem not_model14_eq3267 : Not (Equation3267 (Fin 4)) := by decideFin!
private theorem not_model14_eq3271 : Not (Equation3271 (Fin 4)) := by decideFin!
private theorem not_model14_eq3273 : Not (Equation3273 (Fin 4)) := by decideFin!
private theorem not_model14_eq3274 : Not (Equation3274 (Fin 4)) := by decideFin!
private theorem not_model14_eq3275 : Not (Equation3275 (Fin 4)) := by decideFin!
private theorem not_model14_eq3277 : Not (Equation3277 (Fin 4)) := by decideFin!
private theorem not_model14_eq3278 : Not (Equation3278 (Fin 4)) := by decideFin!
private theorem not_model14_eq3290 : Not (Equation3290 (Fin 4)) := by decideFin!
private theorem not_model14_eq3292 : Not (Equation3292 (Fin 4)) := by decideFin!
private theorem not_model14_eq3300 : Not (Equation3300 (Fin 4)) := by decideFin!
private theorem not_model14_eq3306 : Not (Equation3306 (Fin 4)) := by decideFin!
private theorem not_model14_eq3308 : Not (Equation3308 (Fin 4)) := by decideFin!
private theorem not_model14_eq3309 : Not (Equation3309 (Fin 4)) := by decideFin!
private theorem model14_eq3315 : Equation3315 (Fin 4) := by decideFin!
private theorem model14_eq3316 : Equation3316 (Fin 4) := by decideFin!
private theorem model14_eq3319 : Equation3319 (Fin 4) := by decideFin!
private theorem model14_eq3322 : Equation3322 (Fin 4) := by decideFin!
private theorem model14_eq3323 : Equation3323 (Fin 4) := by decideFin!
private theorem not_model14_eq3326 : Not (Equation3326 (Fin 4)) := by decideFin!
private theorem not_model14_eq3331 : Not (Equation3331 (Fin 4)) := by decideFin!
private theorem not_model14_eq3334 : Not (Equation3334 (Fin 4)) := by decideFin!
private theorem not_model14_eq3342 : Not (Equation3342 (Fin 4)) := by decideFin!
private theorem not_model14_eq3346 : Not (Equation3346 (Fin 4)) := by decideFin!
private theorem not_model14_eq3350 : Not (Equation3350 (Fin 4)) := by decideFin!
private theorem not_model14_eq3353 : Not (Equation3353 (Fin 4)) := by decideFin!
private theorem not_model14_eq3388 : Not (Equation3388 (Fin 4)) := by decideFin!
private theorem not_model14_eq3414 : Not (Equation3414 (Fin 4)) := by decideFin!
private theorem model14_eq4268 : Equation4268 (Fin 4) := by decideFin!
private theorem not_model14_eq4269 : Not (Equation4269 (Fin 4)) := by decideFin!
private theorem not_model14_eq4270 : Not (Equation4270 (Fin 4)) := by decideFin!
private theorem not_model14_eq4271 : Not (Equation4271 (Fin 4)) := by decideFin!
private theorem not_model14_eq4272 : Not (Equation4272 (Fin 4)) := by decideFin!
private theorem not_model14_eq4273 : Not (Equation4273 (Fin 4)) := by decideFin!
private theorem not_model14_eq4274 : Not (Equation4274 (Fin 4)) := by decideFin!
private theorem not_model14_eq4275 : Not (Equation4275 (Fin 4)) := by decideFin!
private theorem not_model14_eq4276 : Not (Equation4276 (Fin 4)) := by decideFin!
private theorem not_model14_eq4277 : Not (Equation4277 (Fin 4)) := by decideFin!
private theorem not_model14_eq4278 : Not (Equation4278 (Fin 4)) := by decideFin!
private theorem not_model14_eq4279 : Not (Equation4279 (Fin 4)) := by decideFin!
private theorem not_model14_eq4280 : Not (Equation4280 (Fin 4)) := by decideFin!
private theorem not_model14_eq4283 : Not (Equation4283 (Fin 4)) := by decideFin!
private theorem not_model14_eq4284 : Not (Equation4284 (Fin 4)) := by decideFin!
private theorem not_model14_eq4286 : Not (Equation4286 (Fin 4)) := by decideFin!
private theorem not_model14_eq4287 : Not (Equation4287 (Fin 4)) := by decideFin!
private theorem not_model14_eq4288 : Not (Equation4288 (Fin 4)) := by decideFin!
private theorem not_model14_eq4290 : Not (Equation4290 (Fin 4)) := by decideFin!
private theorem not_model14_eq4291 : Not (Equation4291 (Fin 4)) := by decideFin!
private theorem not_model14_eq4293 : Not (Equation4293 (Fin 4)) := by decideFin!
private theorem not_model14_eq4296 : Not (Equation4296 (Fin 4)) := by decideFin!
private theorem not_model14_eq4297 : Not (Equation4297 (Fin 4)) := by decideFin!
private theorem not_model14_eq4299 : Not (Equation4299 (Fin 4)) := by decideFin!
private theorem not_model14_eq4300 : Not (Equation4300 (Fin 4)) := by decideFin!
private theorem not_model14_eq4301 : Not (Equation4301 (Fin 4)) := by decideFin!
private theorem not_model14_eq4304 : Not (Equation4304 (Fin 4)) := by decideFin!
private theorem not_model14_eq4305 : Not (Equation4305 (Fin 4)) := by decideFin!
private theorem model14_eq4314 : Equation4314 (Fin 4) := by decideFin!
private theorem model14_eq4315 : Equation4315 (Fin 4) := by decideFin!
private theorem not_model14_eq4318 : Not (Equation4318 (Fin 4)) := by decideFin!
private theorem not_model14_eq4320 : Not (Equation4320 (Fin 4)) := by decideFin!
private theorem not_model14_eq4321 : Not (Equation4321 (Fin 4)) := by decideFin!
private theorem not_model14_eq4325 : Not (Equation4325 (Fin 4)) := by decideFin!
private theorem not_model14_eq4327 : Not (Equation4327 (Fin 4)) := by decideFin!
private theorem not_model14_eq4331 : Not (Equation4331 (Fin 4)) := by decideFin!
private theorem not_model14_eq4343 : Not (Equation4343 (Fin 4)) := by decideFin!
private theorem not_model14_eq4358 : Not (Equation4358 (Fin 4)) := by decideFin!
private theorem not_model14_eq4362 : Not (Equation4362 (Fin 4)) := by decideFin!
private theorem not_model14_eq4364 : Not (Equation4364 (Fin 4)) := by decideFin!
private theorem not_model14_eq4369 : Not (Equation4369 (Fin 4)) := by decideFin!
private theorem model14_eq4512 : Equation4512 (Fin 4) := by decideFin!

theorem model14_at1 : AssociativeTheory1 (Fin 4) :=
  model14_eq4512

theorem not_model14_at2 : Not (AssociativeTheory2 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq2

theorem not_model14_at3 : Not (AssociativeTheory3 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3

theorem not_model14_at4 : Not (AssociativeTheory4 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4

theorem not_model14_at5 : Not (AssociativeTheory5 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq5

theorem not_model14_at6 : Not (AssociativeTheory6 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem not_model14_at7 : Not (AssociativeTheory7 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq10

theorem not_model14_at8 : Not (AssociativeTheory8 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq11

theorem not_model14_at9 : Not (AssociativeTheory9 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq14

theorem not_model14_at10 : Not (AssociativeTheory10 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq16

theorem not_model14_at11 : Not (AssociativeTheory11 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq38

theorem not_model14_at12 : Not (AssociativeTheory12 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq39

theorem not_model14_at13 : Not (AssociativeTheory13 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq38

theorem not_model14_at14 : Not (AssociativeTheory14 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at15 : Not (AssociativeTheory15 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at16 : Not (AssociativeTheory16 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3

theorem not_model14_at17 : Not (AssociativeTheory17 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem not_model14_at18 : Not (AssociativeTheory18 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at19 : Not (AssociativeTheory19 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq47

theorem not_model14_at20 : Not (AssociativeTheory20 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at21 : Not (AssociativeTheory21 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq56

theorem not_model14_at22 : Not (AssociativeTheory22 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at23 : Not (AssociativeTheory23 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq75

theorem not_model14_at24 : Not (AssociativeTheory24 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq56

theorem model14_at25 : AssociativeTheory25 (Fin 4) :=
  ⟨model14_eq307, model14_eq4512⟩

theorem not_model14_at26 : Not (AssociativeTheory26 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at27 : Not (AssociativeTheory27 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at28 : Not (AssociativeTheory28 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem model14_at29 : AssociativeTheory29 (Fin 4) :=
  ⟨model14_eq308, model14_eq4512⟩

theorem not_model14_at30 : Not (AssociativeTheory30 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at31 : Not (AssociativeTheory31 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at32 : Not (AssociativeTheory32 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at33 : Not (AssociativeTheory33 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq310

theorem not_model14_at34 : Not (AssociativeTheory34 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq311

theorem not_model14_at35 : Not (AssociativeTheory35 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at36 : Not (AssociativeTheory36 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at37 : Not (AssociativeTheory37 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq312

theorem not_model14_at38 : Not (AssociativeTheory38 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at39 : Not (AssociativeTheory39 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq315

theorem not_model14_at40 : Not (AssociativeTheory40 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq318

theorem not_model14_at41 : Not (AssociativeTheory41 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at42 : Not (AssociativeTheory42 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at43 : Not (AssociativeTheory43 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at44 : Not (AssociativeTheory44 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq312

theorem model14_at45 : AssociativeTheory45 (Fin 4) :=
  ⟨model14_eq325, model14_eq4512⟩

theorem not_model14_at46 : Not (AssociativeTheory46 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3

theorem model14_at47 : AssociativeTheory47 (Fin 4) :=
  ⟨model14_eq308, model14_eq325, model14_eq4512⟩

theorem not_model14_at48 : Not (AssociativeTheory48 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem model14_at49 : AssociativeTheory49 (Fin 4) :=
  ⟨model14_eq326, model14_eq4512⟩

theorem not_model14_at50 : Not (AssociativeTheory50 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at51 : Not (AssociativeTheory51 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq333

theorem not_model14_at52 : Not (AssociativeTheory52 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3

theorem not_model14_at53 : Not (AssociativeTheory53 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq333

theorem not_model14_at54 : Not (AssociativeTheory54 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq411

theorem not_model14_at55 : Not (AssociativeTheory55 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at56 : Not (AssociativeTheory56 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq419

theorem not_model14_at57 : Not (AssociativeTheory57 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq429

theorem not_model14_at58 : Not (AssociativeTheory58 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq440

theorem not_model14_at59 : Not (AssociativeTheory59 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at60 : Not (AssociativeTheory60 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq504

theorem not_model14_at61 : Not (AssociativeTheory61 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq513

theorem not_model14_at62 : Not (AssociativeTheory62 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq440

theorem model14_at63 : AssociativeTheory63 (Fin 4) :=
  ⟨model14_eq3253, model14_eq4512⟩

theorem not_model14_at64 : Not (AssociativeTheory64 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem model14_at65 : AssociativeTheory65 (Fin 4) :=
  ⟨model14_eq3255, model14_eq4512⟩

theorem model14_at66 : AssociativeTheory66 (Fin 4) :=
  ⟨model14_eq326, model14_eq3255, model14_eq4512⟩

theorem model14_at67 : AssociativeTheory67 (Fin 4) :=
  ⟨model14_eq3256, model14_eq4512⟩

theorem not_model14_at68 : Not (AssociativeTheory68 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3258

theorem not_model14_at69 : Not (AssociativeTheory69 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at70 : Not (AssociativeTheory70 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3258

theorem not_model14_at71 : Not (AssociativeTheory71 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3259

theorem not_model14_at72 : Not (AssociativeTheory72 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3260

theorem not_model14_at73 : Not (AssociativeTheory73 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at74 : Not (AssociativeTheory74 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3261

theorem not_model14_at75 : Not (AssociativeTheory75 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3264

theorem not_model14_at76 : Not (AssociativeTheory76 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at77 : Not (AssociativeTheory77 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3264

theorem not_model14_at78 : Not (AssociativeTheory78 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq312

theorem not_model14_at79 : Not (AssociativeTheory79 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3260

theorem not_model14_at80 : Not (AssociativeTheory80 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at81 : Not (AssociativeTheory81 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3265

theorem not_model14_at82 : Not (AssociativeTheory82 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at83 : Not (AssociativeTheory83 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3260

theorem not_model14_at84 : Not (AssociativeTheory84 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at85 : Not (AssociativeTheory85 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3264

theorem not_model14_at86 : Not (AssociativeTheory86 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at87 : Not (AssociativeTheory87 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3260

theorem not_model14_at88 : Not (AssociativeTheory88 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at89 : Not (AssociativeTheory89 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at90 : Not (AssociativeTheory90 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at91 : Not (AssociativeTheory91 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at92 : Not (AssociativeTheory92 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at93 : Not (AssociativeTheory93 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at94 : Not (AssociativeTheory94 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3271

theorem not_model14_at95 : Not (AssociativeTheory95 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3274

theorem not_model14_at96 : Not (AssociativeTheory96 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3264

theorem not_model14_at97 : Not (AssociativeTheory97 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3278

theorem not_model14_at98 : Not (AssociativeTheory98 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3292

theorem not_model14_at99 : Not (AssociativeTheory99 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3264

theorem not_model14_at100 : Not (AssociativeTheory100 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3274

theorem not_model14_at101 : Not (AssociativeTheory101 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3264

theorem not_model14_at102 : Not (AssociativeTheory102 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3300

theorem not_model14_at103 : Not (AssociativeTheory103 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at104 : Not (AssociativeTheory104 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem not_model14_at105 : Not (AssociativeTheory105 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at106 : Not (AssociativeTheory106 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at107 : Not (AssociativeTheory107 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem not_model14_at108 : Not (AssociativeTheory108 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3261

theorem not_model14_at109 : Not (AssociativeTheory109 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3271

theorem not_model14_at110 : Not (AssociativeTheory110 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3278

theorem not_model14_at111 : Not (AssociativeTheory111 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3308

theorem not_model14_at112 : Not (AssociativeTheory112 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem model14_at113 : AssociativeTheory113 (Fin 4) :=
  ⟨model14_eq3315, model14_eq4512⟩

theorem not_model14_at114 : Not (AssociativeTheory114 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem model14_at115 : AssociativeTheory115 (Fin 4) :=
  ⟨model14_eq3256, model14_eq3315, model14_eq4512⟩

theorem not_model14_at116 : Not (AssociativeTheory116 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem model14_at117 : AssociativeTheory117 (Fin 4) :=
  ⟨model14_eq3316, model14_eq4512⟩

theorem not_model14_at118 : Not (AssociativeTheory118 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem model14_at119 : AssociativeTheory119 (Fin 4) :=
  ⟨model14_eq326, model14_eq3316, model14_eq4512⟩

theorem model14_at120 : AssociativeTheory120 (Fin 4) :=
  ⟨model14_eq3319, model14_eq4512⟩

theorem not_model14_at121 : Not (AssociativeTheory121 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem not_model14_at122 : Not (AssociativeTheory122 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3346

theorem not_model14_at123 : Not (AssociativeTheory123 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem not_model14_at124 : Not (AssociativeTheory124 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3353

theorem not_model14_at125 : Not (AssociativeTheory125 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem not_model14_at126 : Not (AssociativeTheory126 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3353

theorem model14_at127 : AssociativeTheory127 (Fin 4) :=
  ⟨model14_eq4268, model14_eq4512⟩

theorem not_model14_at128 : Not (AssociativeTheory128 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at129 : Not (AssociativeTheory129 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at130 : Not (AssociativeTheory130 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at131 : Not (AssociativeTheory131 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at132 : Not (AssociativeTheory132 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at133 : Not (AssociativeTheory133 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at134 : Not (AssociativeTheory134 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at135 : Not (AssociativeTheory135 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at136 : Not (AssociativeTheory136 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4271

theorem not_model14_at137 : Not (AssociativeTheory137 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at138 : Not (AssociativeTheory138 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at139 : Not (AssociativeTheory139 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at140 : Not (AssociativeTheory140 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at141 : Not (AssociativeTheory141 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at142 : Not (AssociativeTheory142 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at143 : Not (AssociativeTheory143 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at144 : Not (AssociativeTheory144 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4271

theorem not_model14_at145 : Not (AssociativeTheory145 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at146 : Not (AssociativeTheory146 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at147 : Not (AssociativeTheory147 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at148 : Not (AssociativeTheory148 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at149 : Not (AssociativeTheory149 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at150 : Not (AssociativeTheory150 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4275

theorem not_model14_at151 : Not (AssociativeTheory151 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4275

theorem not_model14_at152 : Not (AssociativeTheory152 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at153 : Not (AssociativeTheory153 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at154 : Not (AssociativeTheory154 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at155 : Not (AssociativeTheory155 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at156 : Not (AssociativeTheory156 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at157 : Not (AssociativeTheory157 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at158 : Not (AssociativeTheory158 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at159 : Not (AssociativeTheory159 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at160 : Not (AssociativeTheory160 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4278

theorem not_model14_at161 : Not (AssociativeTheory161 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at162 : Not (AssociativeTheory162 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq47

theorem not_model14_at163 : Not (AssociativeTheory163 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq56

theorem not_model14_at164 : Not (AssociativeTheory164 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at165 : Not (AssociativeTheory165 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at166 : Not (AssociativeTheory166 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq411

theorem not_model14_at167 : Not (AssociativeTheory167 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq440

theorem not_model14_at168 : Not (AssociativeTheory168 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at169 : Not (AssociativeTheory169 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at170 : Not (AssociativeTheory170 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at171 : Not (AssociativeTheory171 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at172 : Not (AssociativeTheory172 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at173 : Not (AssociativeTheory173 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at174 : Not (AssociativeTheory174 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at175 : Not (AssociativeTheory175 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at176 : Not (AssociativeTheory176 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at177 : Not (AssociativeTheory177 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at178 : Not (AssociativeTheory178 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at179 : Not (AssociativeTheory179 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at180 : Not (AssociativeTheory180 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at181 : Not (AssociativeTheory181 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq43

theorem not_model14_at182 : Not (AssociativeTheory182 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at183 : Not (AssociativeTheory183 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at184 : Not (AssociativeTheory184 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at185 : Not (AssociativeTheory185 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4287

theorem not_model14_at186 : Not (AssociativeTheory186 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4287

theorem not_model14_at187 : Not (AssociativeTheory187 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at188 : Not (AssociativeTheory188 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at189 : Not (AssociativeTheory189 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq411

theorem not_model14_at190 : Not (AssociativeTheory190 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at191 : Not (AssociativeTheory191 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at192 : Not (AssociativeTheory192 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at193 : Not (AssociativeTheory193 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at194 : Not (AssociativeTheory194 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at195 : Not (AssociativeTheory195 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at196 : Not (AssociativeTheory196 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at197 : Not (AssociativeTheory197 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at198 : Not (AssociativeTheory198 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at199 : Not (AssociativeTheory199 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at200 : Not (AssociativeTheory200 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at201 : Not (AssociativeTheory201 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at202 : Not (AssociativeTheory202 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at203 : Not (AssociativeTheory203 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at204 : Not (AssociativeTheory204 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at205 : Not (AssociativeTheory205 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at206 : Not (AssociativeTheory206 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at207 : Not (AssociativeTheory207 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq312

theorem not_model14_at208 : Not (AssociativeTheory208 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at209 : Not (AssociativeTheory209 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at210 : Not (AssociativeTheory210 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at211 : Not (AssociativeTheory211 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at212 : Not (AssociativeTheory212 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at213 : Not (AssociativeTheory213 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at214 : Not (AssociativeTheory214 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at215 : Not (AssociativeTheory215 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at216 : Not (AssociativeTheory216 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at217 : Not (AssociativeTheory217 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at218 : Not (AssociativeTheory218 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at219 : Not (AssociativeTheory219 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at220 : Not (AssociativeTheory220 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at221 : Not (AssociativeTheory221 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at222 : Not (AssociativeTheory222 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at223 : Not (AssociativeTheory223 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at224 : Not (AssociativeTheory224 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at225 : Not (AssociativeTheory225 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at226 : Not (AssociativeTheory226 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at227 : Not (AssociativeTheory227 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at228 : Not (AssociativeTheory228 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4300

theorem not_model14_at229 : Not (AssociativeTheory229 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4300

theorem model14_at230 : AssociativeTheory230 (Fin 4) :=
  ⟨model14_eq4314, model14_eq4512⟩

theorem model14_at231 : AssociativeTheory231 (Fin 4) :=
  ⟨model14_eq307, model14_eq4314, model14_eq4512⟩

theorem model14_at232 : AssociativeTheory232 (Fin 4) :=
  ⟨model14_eq308, model14_eq4314, model14_eq4512⟩

theorem not_model14_at233 : Not (AssociativeTheory233 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem model14_at234 : AssociativeTheory234 (Fin 4) :=
  ⟨model14_eq4268, model14_eq4314, model14_eq4512⟩

theorem not_model14_at235 : Not (AssociativeTheory235 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4275

theorem not_model14_at236 : Not (AssociativeTheory236 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at237 : Not (AssociativeTheory237 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at238 : Not (AssociativeTheory238 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem model14_at239 : AssociativeTheory239 (Fin 4) :=
  ⟨model14_eq4315, model14_eq4512⟩

theorem model14_at240 : AssociativeTheory240 (Fin 4) :=
  ⟨model14_eq307, model14_eq4315, model14_eq4512⟩

theorem not_model14_at241 : Not (AssociativeTheory241 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at242 : Not (AssociativeTheory242 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq47

theorem not_model14_at243 : Not (AssociativeTheory243 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq75

theorem not_model14_at244 : Not (AssociativeTheory244 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at245 : Not (AssociativeTheory245 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at246 : Not (AssociativeTheory246 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq411

theorem not_model14_at247 : Not (AssociativeTheory247 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq513

theorem not_model14_at248 : Not (AssociativeTheory248 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at249 : Not (AssociativeTheory249 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3261

theorem not_model14_at250 : Not (AssociativeTheory250 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem not_model14_at251 : Not (AssociativeTheory251 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at252 : Not (AssociativeTheory252 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4275

theorem not_model14_at253 : Not (AssociativeTheory253 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at254 : Not (AssociativeTheory254 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at255 : Not (AssociativeTheory255 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at256 : Not (AssociativeTheory256 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at257 : Not (AssociativeTheory257 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at258 : Not (AssociativeTheory258 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at259 : Not (AssociativeTheory259 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4320

theorem not_model14_at260 : Not (AssociativeTheory260 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at261 : Not (AssociativeTheory261 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at262 : Not (AssociativeTheory262 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at263 : Not (AssociativeTheory263 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at264 : Not (AssociativeTheory264 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at265 : Not (AssociativeTheory265 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at266 : Not (AssociativeTheory266 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3260

theorem not_model14_at267 : Not (AssociativeTheory267 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3265

theorem not_model14_at268 : Not (AssociativeTheory268 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3260

theorem not_model14_at269 : Not (AssociativeTheory269 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at270 : Not (AssociativeTheory270 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at271 : Not (AssociativeTheory271 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at272 : Not (AssociativeTheory272 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at273 : Not (AssociativeTheory273 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at274 : Not (AssociativeTheory274 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at275 : Not (AssociativeTheory275 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at276 : Not (AssociativeTheory276 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at277 : Not (AssociativeTheory277 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at278 : Not (AssociativeTheory278 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at279 : Not (AssociativeTheory279 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at280 : Not (AssociativeTheory280 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at281 : Not (AssociativeTheory281 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at282 : Not (AssociativeTheory282 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at283 : Not (AssociativeTheory283 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at284 : Not (AssociativeTheory284 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at285 : Not (AssociativeTheory285 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4343

theorem not_model14_at286 : Not (AssociativeTheory286 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4343

theorem not_model14_at287 : Not (AssociativeTheory287 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4343

theorem not_model14_at288 : Not (AssociativeTheory288 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at289 : Not (AssociativeTheory289 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at290 : Not (AssociativeTheory290 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at291 : Not (AssociativeTheory291 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at292 : Not (AssociativeTheory292 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at293 : Not (AssociativeTheory293 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at294 : Not (AssociativeTheory294 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at295 : Not (AssociativeTheory295 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at296 : Not (AssociativeTheory296 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at297 : Not (AssociativeTheory297 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at298 : Not (AssociativeTheory298 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at299 : Not (AssociativeTheory299 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at300 : Not (AssociativeTheory300 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at301 : Not (AssociativeTheory301 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at302 : Not (AssociativeTheory302 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at303 : Not (AssociativeTheory303 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at304 : Not (AssociativeTheory304 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at305 : Not (AssociativeTheory305 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at306 : Not (AssociativeTheory306 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at307 : Not (AssociativeTheory307 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3

theorem not_model14_at308 : Not (AssociativeTheory308 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem not_model14_at309 : Not (AssociativeTheory309 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at310 : Not (AssociativeTheory310 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq47

theorem not_model14_at311 : Not (AssociativeTheory311 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at312 : Not (AssociativeTheory312 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at313 : Not (AssociativeTheory313 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at314 : Not (AssociativeTheory314 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at315 : Not (AssociativeTheory315 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at316 : Not (AssociativeTheory316 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq411

theorem not_model14_at317 : Not (AssociativeTheory317 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at318 : Not (AssociativeTheory318 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at319 : Not (AssociativeTheory319 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at320 : Not (AssociativeTheory320 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at321 : Not (AssociativeTheory321 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem not_model14_at322 : Not (AssociativeTheory322 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at323 : Not (AssociativeTheory323 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at324 : Not (AssociativeTheory324 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at325 : Not (AssociativeTheory325 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at326 : Not (AssociativeTheory326 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at327 : Not (AssociativeTheory327 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4272

theorem not_model14_at328 : Not (AssociativeTheory328 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at329 : Not (AssociativeTheory329 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at330 : Not (AssociativeTheory330 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at331 : Not (AssociativeTheory331 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at332 : Not (AssociativeTheory332 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at333 : Not (AssociativeTheory333 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at334 : Not (AssociativeTheory334 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at335 : Not (AssociativeTheory335 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at336 : Not (AssociativeTheory336 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at337 : Not (AssociativeTheory337 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4290

theorem not_model14_at338 : Not (AssociativeTheory338 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at339 : Not (AssociativeTheory339 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at340 : Not (AssociativeTheory340 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at341 : Not (AssociativeTheory341 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at342 : Not (AssociativeTheory342 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at343 : Not (AssociativeTheory343 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at344 : Not (AssociativeTheory344 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at345 : Not (AssociativeTheory345 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at346 : Not (AssociativeTheory346 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4343

theorem not_model14_at347 : Not (AssociativeTheory347 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4343

theorem not_model14_at348 : Not (AssociativeTheory348 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at349 : Not (AssociativeTheory349 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at350 : Not (AssociativeTheory350 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at351 : Not (AssociativeTheory351 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at352 : Not (AssociativeTheory352 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3

theorem not_model14_at353 : Not (AssociativeTheory353 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq8

theorem not_model14_at354 : Not (AssociativeTheory354 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at355 : Not (AssociativeTheory355 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq47

theorem not_model14_at356 : Not (AssociativeTheory356 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at357 : Not (AssociativeTheory357 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at358 : Not (AssociativeTheory358 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at359 : Not (AssociativeTheory359 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq323

theorem not_model14_at360 : Not (AssociativeTheory360 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at361 : Not (AssociativeTheory361 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq411

theorem not_model14_at362 : Not (AssociativeTheory362 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at363 : Not (AssociativeTheory363 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3261

theorem not_model14_at364 : Not (AssociativeTheory364 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at365 : Not (AssociativeTheory365 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3300

theorem not_model14_at366 : Not (AssociativeTheory366 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3306

theorem not_model14_at367 : Not (AssociativeTheory367 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at368 : Not (AssociativeTheory368 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at369 : Not (AssociativeTheory369 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at370 : Not (AssociativeTheory370 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at371 : Not (AssociativeTheory371 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at372 : Not (AssociativeTheory372 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at373 : Not (AssociativeTheory373 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4275

theorem not_model14_at374 : Not (AssociativeTheory374 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at375 : Not (AssociativeTheory375 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at376 : Not (AssociativeTheory376 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at377 : Not (AssociativeTheory377 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at378 : Not (AssociativeTheory378 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at379 : Not (AssociativeTheory379 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at380 : Not (AssociativeTheory380 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at381 : Not (AssociativeTheory381 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at382 : Not (AssociativeTheory382 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at383 : Not (AssociativeTheory383 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at384 : Not (AssociativeTheory384 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at385 : Not (AssociativeTheory385 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at386 : Not (AssociativeTheory386 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at387 : Not (AssociativeTheory387 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at388 : Not (AssociativeTheory388 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at389 : Not (AssociativeTheory389 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at390 : Not (AssociativeTheory390 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at391 : Not (AssociativeTheory391 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at392 : Not (AssociativeTheory392 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4362

theorem not_model14_at393 : Not (AssociativeTheory393 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at394 : Not (AssociativeTheory394 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4293

theorem not_model14_at395 : Not (AssociativeTheory395 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at396 : Not (AssociativeTheory396 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at397 : Not (AssociativeTheory397 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at398 : Not (AssociativeTheory398 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at399 : Not (AssociativeTheory399 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at400 : Not (AssociativeTheory400 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at401 : Not (AssociativeTheory401 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at402 : Not (AssociativeTheory402 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4358

theorem not_model14_at403 : Not (AssociativeTheory403 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at404 : Not (AssociativeTheory404 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at405 : Not (AssociativeTheory405 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at406 : Not (AssociativeTheory406 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at407 : Not (AssociativeTheory407 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at408 : Not (AssociativeTheory408 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4364

theorem not_model14_at409 : Not (AssociativeTheory409 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at410 : Not (AssociativeTheory410 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4364

theorem not_model14_at411 : Not (AssociativeTheory411 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at412 : Not (AssociativeTheory412 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4364

theorem not_model14_at413 : Not (AssociativeTheory413 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at414 : Not (AssociativeTheory414 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4364

theorem not_model14_at415 : Not (AssociativeTheory415 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at416 : Not (AssociativeTheory416 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at417 : Not (AssociativeTheory417 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at418 : Not (AssociativeTheory418 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at419 : Not (AssociativeTheory419 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at420 : Not (AssociativeTheory420 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4369

theorem not_model14_at421 : Not (AssociativeTheory421 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at422 : Not (AssociativeTheory422 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4369

theorem not_model14_at423 : Not (AssociativeTheory423 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at424 : Not (AssociativeTheory424 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at425 : Not (AssociativeTheory425 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4369

theorem not_model14_at426 : Not (AssociativeTheory426 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at427 : Not (AssociativeTheory427 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq309

theorem not_model14_at428 : Not (AssociativeTheory428 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4369

theorem not_model14_at429 : Not (AssociativeTheory429 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at430 : Not (AssociativeTheory430 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at431 : Not (AssociativeTheory431 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at432 : Not (AssociativeTheory432 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4273

theorem not_model14_at433 : Not (AssociativeTheory433 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at434 : Not (AssociativeTheory434 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4270

theorem not_model14_at435 : Not (AssociativeTheory435 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at436 : Not (AssociativeTheory436 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at437 : Not (AssociativeTheory437 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at438 : Not (AssociativeTheory438 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at439 : Not (AssociativeTheory439 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at440 : Not (AssociativeTheory440 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at441 : Not (AssociativeTheory441 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at442 : Not (AssociativeTheory442 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4269

theorem not_model14_at443 : Not (AssociativeTheory443 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at444 : Not (AssociativeTheory444 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at445 : Not (AssociativeTheory445 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4283

theorem not_model14_at446 : Not (AssociativeTheory446 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at447 : Not (AssociativeTheory447 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4291

theorem not_model14_at448 : Not (AssociativeTheory448 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at449 : Not (AssociativeTheory449 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at450 : Not (AssociativeTheory450 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq40

theorem not_model14_at451 : Not (AssociativeTheory451 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at452 : Not (AssociativeTheory452 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq3267

theorem not_model14_at453 : Not (AssociativeTheory453 (Fin 4)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4321

theorem not_model14_at454 : Not (AssociativeTheory454 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276

theorem not_model14_at455 : Not (AssociativeTheory455 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4284

theorem not_model14_at456 : Not (AssociativeTheory456 (Fin 4)) := by
  refine not_and_of_not_left _ ?_
  exact not_model14_eq4276
