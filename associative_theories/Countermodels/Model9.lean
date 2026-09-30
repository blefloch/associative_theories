import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model9_op := finOpTable "[[0,0,0],[1,1,1],[0,1,2]]"
private def model9 : Magma (Fin 3) where op := model9_op
private instance : Magma (Fin 3) := model9

private theorem model9_eq1 : Equation1 (Fin 3) := by decideFin!
private theorem model9_eq3 : Equation3 (Fin 3) := by decideFin!
private theorem model9_eq8 : Equation8 (Fin 3) := by decideFin!
private theorem model9_eq47 : Equation47 (Fin 3) := by decideFin!
private theorem model9_eq307 : Equation307 (Fin 3) := by decideFin!
private theorem model9_eq323 : Equation323 (Fin 3) := by decideFin!
private theorem model9_eq325 : Equation325 (Fin 3) := by decideFin!
private theorem model9_eq326 : Equation326 (Fin 3) := by decideFin!
private theorem model9_eq411 : Equation411 (Fin 3) := by decideFin!
private theorem model9_eq3253 : Equation3253 (Fin 3) := by decideFin!
private theorem model9_eq3306 : Equation3306 (Fin 3) := by decideFin!
private theorem model9_eq3308 : Equation3308 (Fin 3) := by decideFin!
private theorem model9_eq3309 : Equation3309 (Fin 3) := by decideFin!
private theorem model9_eq3315 : Equation3315 (Fin 3) := by decideFin!
private theorem model9_eq3316 : Equation3316 (Fin 3) := by decideFin!
private theorem model9_eq3319 : Equation3319 (Fin 3) := by decideFin!
private theorem model9_eq4283 : Equation4283 (Fin 3) := by decideFin!
private theorem model9_eq4284 : Equation4284 (Fin 3) := by decideFin!
private theorem model9_eq4314 : Equation4314 (Fin 3) := by decideFin!
private theorem model9_eq4512 : Equation4512 (Fin 3) := by decideFin!
private theorem not_model9_eq2 : Not (Equation2 (Fin 3)) := by decideFin!
private theorem not_model9_eq4 : Not (Equation4 (Fin 3)) := by decideFin!
private theorem not_model9_eq5 : Not (Equation5 (Fin 3)) := by decideFin!
private theorem not_model9_eq10 : Not (Equation10 (Fin 3)) := by decideFin!
private theorem not_model9_eq11 : Not (Equation11 (Fin 3)) := by decideFin!
private theorem not_model9_eq14 : Not (Equation14 (Fin 3)) := by decideFin!
private theorem not_model9_eq16 : Not (Equation16 (Fin 3)) := by decideFin!
private theorem not_model9_eq38 : Not (Equation38 (Fin 3)) := by decideFin!
private theorem not_model9_eq39 : Not (Equation39 (Fin 3)) := by decideFin!
private theorem not_model9_eq40 : Not (Equation40 (Fin 3)) := by decideFin!
private theorem not_model9_eq41 : Not (Equation41 (Fin 3)) := by decideFin!
private theorem not_model9_eq43 : Not (Equation43 (Fin 3)) := by decideFin!
private theorem not_model9_eq56 : Not (Equation56 (Fin 3)) := by decideFin!
private theorem not_model9_eq66 : Not (Equation66 (Fin 3)) := by decideFin!
private theorem not_model9_eq75 : Not (Equation75 (Fin 3)) := by decideFin!
private theorem not_model9_eq308 : Not (Equation308 (Fin 3)) := by decideFin!
private theorem not_model9_eq309 : Not (Equation309 (Fin 3)) := by decideFin!
private theorem not_model9_eq310 : Not (Equation310 (Fin 3)) := by decideFin!
private theorem not_model9_eq311 : Not (Equation311 (Fin 3)) := by decideFin!
private theorem not_model9_eq312 : Not (Equation312 (Fin 3)) := by decideFin!
private theorem not_model9_eq313 : Not (Equation313 (Fin 3)) := by decideFin!
private theorem not_model9_eq314 : Not (Equation314 (Fin 3)) := by decideFin!
private theorem not_model9_eq315 : Not (Equation315 (Fin 3)) := by decideFin!
private theorem not_model9_eq316 : Not (Equation316 (Fin 3)) := by decideFin!
private theorem not_model9_eq318 : Not (Equation318 (Fin 3)) := by decideFin!
private theorem not_model9_eq327 : Not (Equation327 (Fin 3)) := by decideFin!
private theorem not_model9_eq329 : Not (Equation329 (Fin 3)) := by decideFin!
private theorem not_model9_eq332 : Not (Equation332 (Fin 3)) := by decideFin!
private theorem not_model9_eq333 : Not (Equation333 (Fin 3)) := by decideFin!
private theorem not_model9_eq343 : Not (Equation343 (Fin 3)) := by decideFin!
private theorem not_model9_eq419 : Not (Equation419 (Fin 3)) := by decideFin!
private theorem not_model9_eq429 : Not (Equation429 (Fin 3)) := by decideFin!
private theorem not_model9_eq440 : Not (Equation440 (Fin 3)) := by decideFin!
private theorem not_model9_eq477 : Not (Equation477 (Fin 3)) := by decideFin!
private theorem not_model9_eq504 : Not (Equation504 (Fin 3)) := by decideFin!
private theorem not_model9_eq513 : Not (Equation513 (Fin 3)) := by decideFin!
private theorem not_model9_eq3255 : Not (Equation3255 (Fin 3)) := by decideFin!
private theorem not_model9_eq3256 : Not (Equation3256 (Fin 3)) := by decideFin!
private theorem not_model9_eq3258 : Not (Equation3258 (Fin 3)) := by decideFin!
private theorem not_model9_eq3259 : Not (Equation3259 (Fin 3)) := by decideFin!
private theorem not_model9_eq3260 : Not (Equation3260 (Fin 3)) := by decideFin!
private theorem not_model9_eq3261 : Not (Equation3261 (Fin 3)) := by decideFin!
private theorem not_model9_eq3264 : Not (Equation3264 (Fin 3)) := by decideFin!
private theorem not_model9_eq3265 : Not (Equation3265 (Fin 3)) := by decideFin!
private theorem not_model9_eq3267 : Not (Equation3267 (Fin 3)) := by decideFin!
private theorem not_model9_eq3271 : Not (Equation3271 (Fin 3)) := by decideFin!
private theorem not_model9_eq3273 : Not (Equation3273 (Fin 3)) := by decideFin!
private theorem not_model9_eq3274 : Not (Equation3274 (Fin 3)) := by decideFin!
private theorem not_model9_eq3275 : Not (Equation3275 (Fin 3)) := by decideFin!
private theorem not_model9_eq3277 : Not (Equation3277 (Fin 3)) := by decideFin!
private theorem not_model9_eq3278 : Not (Equation3278 (Fin 3)) := by decideFin!
private theorem not_model9_eq3290 : Not (Equation3290 (Fin 3)) := by decideFin!
private theorem not_model9_eq3292 : Not (Equation3292 (Fin 3)) := by decideFin!
private theorem not_model9_eq3300 : Not (Equation3300 (Fin 3)) := by decideFin!
private theorem not_model9_eq3322 : Not (Equation3322 (Fin 3)) := by decideFin!
private theorem not_model9_eq3323 : Not (Equation3323 (Fin 3)) := by decideFin!
private theorem not_model9_eq3326 : Not (Equation3326 (Fin 3)) := by decideFin!
private theorem not_model9_eq3331 : Not (Equation3331 (Fin 3)) := by decideFin!
private theorem not_model9_eq3334 : Not (Equation3334 (Fin 3)) := by decideFin!
private theorem not_model9_eq3342 : Not (Equation3342 (Fin 3)) := by decideFin!
private theorem not_model9_eq3346 : Not (Equation3346 (Fin 3)) := by decideFin!
private theorem not_model9_eq3350 : Not (Equation3350 (Fin 3)) := by decideFin!
private theorem not_model9_eq3353 : Not (Equation3353 (Fin 3)) := by decideFin!
private theorem not_model9_eq3388 : Not (Equation3388 (Fin 3)) := by decideFin!
private theorem not_model9_eq3414 : Not (Equation3414 (Fin 3)) := by decideFin!
private theorem not_model9_eq4268 : Not (Equation4268 (Fin 3)) := by decideFin!
private theorem not_model9_eq4269 : Not (Equation4269 (Fin 3)) := by decideFin!
private theorem not_model9_eq4270 : Not (Equation4270 (Fin 3)) := by decideFin!
private theorem not_model9_eq4271 : Not (Equation4271 (Fin 3)) := by decideFin!
private theorem not_model9_eq4272 : Not (Equation4272 (Fin 3)) := by decideFin!
private theorem not_model9_eq4273 : Not (Equation4273 (Fin 3)) := by decideFin!
private theorem not_model9_eq4274 : Not (Equation4274 (Fin 3)) := by decideFin!
private theorem not_model9_eq4275 : Not (Equation4275 (Fin 3)) := by decideFin!
private theorem not_model9_eq4276 : Not (Equation4276 (Fin 3)) := by decideFin!
private theorem not_model9_eq4277 : Not (Equation4277 (Fin 3)) := by decideFin!
private theorem not_model9_eq4278 : Not (Equation4278 (Fin 3)) := by decideFin!
private theorem not_model9_eq4279 : Not (Equation4279 (Fin 3)) := by decideFin!
private theorem not_model9_eq4280 : Not (Equation4280 (Fin 3)) := by decideFin!
private theorem not_model9_eq4286 : Not (Equation4286 (Fin 3)) := by decideFin!
private theorem not_model9_eq4287 : Not (Equation4287 (Fin 3)) := by decideFin!
private theorem not_model9_eq4288 : Not (Equation4288 (Fin 3)) := by decideFin!
private theorem not_model9_eq4290 : Not (Equation4290 (Fin 3)) := by decideFin!
private theorem not_model9_eq4291 : Not (Equation4291 (Fin 3)) := by decideFin!
private theorem not_model9_eq4293 : Not (Equation4293 (Fin 3)) := by decideFin!
private theorem not_model9_eq4296 : Not (Equation4296 (Fin 3)) := by decideFin!
private theorem not_model9_eq4297 : Not (Equation4297 (Fin 3)) := by decideFin!
private theorem not_model9_eq4299 : Not (Equation4299 (Fin 3)) := by decideFin!
private theorem not_model9_eq4300 : Not (Equation4300 (Fin 3)) := by decideFin!
private theorem not_model9_eq4301 : Not (Equation4301 (Fin 3)) := by decideFin!
private theorem not_model9_eq4304 : Not (Equation4304 (Fin 3)) := by decideFin!
private theorem not_model9_eq4305 : Not (Equation4305 (Fin 3)) := by decideFin!
private theorem not_model9_eq4315 : Not (Equation4315 (Fin 3)) := by decideFin!
private theorem not_model9_eq4318 : Not (Equation4318 (Fin 3)) := by decideFin!
private theorem not_model9_eq4320 : Not (Equation4320 (Fin 3)) := by decideFin!
private theorem not_model9_eq4321 : Not (Equation4321 (Fin 3)) := by decideFin!
private theorem not_model9_eq4325 : Not (Equation4325 (Fin 3)) := by decideFin!
private theorem not_model9_eq4327 : Not (Equation4327 (Fin 3)) := by decideFin!
private theorem not_model9_eq4331 : Not (Equation4331 (Fin 3)) := by decideFin!
private theorem not_model9_eq4343 : Not (Equation4343 (Fin 3)) := by decideFin!
private theorem not_model9_eq4358 : Not (Equation4358 (Fin 3)) := by decideFin!
private theorem not_model9_eq4362 : Not (Equation4362 (Fin 3)) := by decideFin!
private theorem not_model9_eq4364 : Not (Equation4364 (Fin 3)) := by decideFin!
private theorem not_model9_eq4369 : Not (Equation4369 (Fin 3)) := by decideFin!

theorem model9_at1 : AssociativeTheory1 (Fin 3) :=
  model9_eq4512

theorem not_model9_at2 : Not (AssociativeTheory2 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq2

theorem model9_at3 : AssociativeTheory3 (Fin 3) :=
  ⟨model9_eq3, model9_eq4512⟩

theorem not_model9_at4 : Not (AssociativeTheory4 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4

theorem not_model9_at5 : Not (AssociativeTheory5 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq5

theorem model9_at6 : AssociativeTheory6 (Fin 3) :=
  ⟨model9_eq8, model9_eq4512⟩

theorem not_model9_at7 : Not (AssociativeTheory7 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq10

theorem not_model9_at8 : Not (AssociativeTheory8 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq11

theorem not_model9_at9 : Not (AssociativeTheory9 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq14

theorem not_model9_at10 : Not (AssociativeTheory10 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq16

theorem not_model9_at11 : Not (AssociativeTheory11 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq38

theorem not_model9_at12 : Not (AssociativeTheory12 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq39

theorem not_model9_at13 : Not (AssociativeTheory13 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq38

theorem not_model9_at14 : Not (AssociativeTheory14 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at15 : Not (AssociativeTheory15 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at16 : Not (AssociativeTheory16 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at17 : Not (AssociativeTheory17 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at18 : Not (AssociativeTheory18 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem model9_at19 : AssociativeTheory19 (Fin 3) :=
  ⟨model9_eq47, model9_eq4512⟩

theorem not_model9_at20 : Not (AssociativeTheory20 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at21 : Not (AssociativeTheory21 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq56

theorem not_model9_at22 : Not (AssociativeTheory22 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at23 : Not (AssociativeTheory23 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq75

theorem not_model9_at24 : Not (AssociativeTheory24 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq56

theorem model9_at25 : AssociativeTheory25 (Fin 3) :=
  ⟨model9_eq307, model9_eq4512⟩

theorem not_model9_at26 : Not (AssociativeTheory26 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at27 : Not (AssociativeTheory27 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at28 : Not (AssociativeTheory28 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at29 : Not (AssociativeTheory29 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq308

theorem not_model9_at30 : Not (AssociativeTheory30 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at31 : Not (AssociativeTheory31 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at32 : Not (AssociativeTheory32 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq308

theorem not_model9_at33 : Not (AssociativeTheory33 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq310

theorem not_model9_at34 : Not (AssociativeTheory34 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq311

theorem not_model9_at35 : Not (AssociativeTheory35 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at36 : Not (AssociativeTheory36 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at37 : Not (AssociativeTheory37 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq312

theorem not_model9_at38 : Not (AssociativeTheory38 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at39 : Not (AssociativeTheory39 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq315

theorem not_model9_at40 : Not (AssociativeTheory40 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq318

theorem model9_at41 : AssociativeTheory41 (Fin 3) :=
  ⟨model9_eq323, model9_eq4512⟩

theorem not_model9_at42 : Not (AssociativeTheory42 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at43 : Not (AssociativeTheory43 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at44 : Not (AssociativeTheory44 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq312

theorem model9_at45 : AssociativeTheory45 (Fin 3) :=
  ⟨model9_eq325, model9_eq4512⟩

theorem model9_at46 : AssociativeTheory46 (Fin 3) :=
  ⟨model9_eq3, model9_eq325, model9_eq4512⟩

theorem not_model9_at47 : Not (AssociativeTheory47 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq308

theorem model9_at48 : AssociativeTheory48 (Fin 3) :=
  ⟨model9_eq323, model9_eq325, model9_eq4512⟩

theorem model9_at49 : AssociativeTheory49 (Fin 3) :=
  ⟨model9_eq326, model9_eq4512⟩

theorem model9_at50 : AssociativeTheory50 (Fin 3) :=
  ⟨model9_eq323, model9_eq326, model9_eq4512⟩

theorem not_model9_at51 : Not (AssociativeTheory51 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq333

theorem not_model9_at52 : Not (AssociativeTheory52 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq333

theorem not_model9_at53 : Not (AssociativeTheory53 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq333

theorem model9_at54 : AssociativeTheory54 (Fin 3) :=
  ⟨model9_eq411, model9_eq4512⟩

theorem not_model9_at55 : Not (AssociativeTheory55 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at56 : Not (AssociativeTheory56 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq419

theorem not_model9_at57 : Not (AssociativeTheory57 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq429

theorem not_model9_at58 : Not (AssociativeTheory58 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq440

theorem not_model9_at59 : Not (AssociativeTheory59 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at60 : Not (AssociativeTheory60 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq504

theorem not_model9_at61 : Not (AssociativeTheory61 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq513

theorem not_model9_at62 : Not (AssociativeTheory62 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq440

theorem model9_at63 : AssociativeTheory63 (Fin 3) :=
  ⟨model9_eq3253, model9_eq4512⟩

theorem not_model9_at64 : Not (AssociativeTheory64 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at65 : Not (AssociativeTheory65 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3255

theorem not_model9_at66 : Not (AssociativeTheory66 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3255

theorem not_model9_at67 : Not (AssociativeTheory67 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3256

theorem not_model9_at68 : Not (AssociativeTheory68 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3258

theorem not_model9_at69 : Not (AssociativeTheory69 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3258

theorem not_model9_at70 : Not (AssociativeTheory70 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3255

theorem not_model9_at71 : Not (AssociativeTheory71 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3259

theorem not_model9_at72 : Not (AssociativeTheory72 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3260

theorem not_model9_at73 : Not (AssociativeTheory73 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at74 : Not (AssociativeTheory74 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3261

theorem not_model9_at75 : Not (AssociativeTheory75 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3264

theorem not_model9_at76 : Not (AssociativeTheory76 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at77 : Not (AssociativeTheory77 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq308

theorem not_model9_at78 : Not (AssociativeTheory78 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq312

theorem not_model9_at79 : Not (AssociativeTheory79 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3260

theorem not_model9_at80 : Not (AssociativeTheory80 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at81 : Not (AssociativeTheory81 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3265

theorem not_model9_at82 : Not (AssociativeTheory82 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at83 : Not (AssociativeTheory83 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3260

theorem not_model9_at84 : Not (AssociativeTheory84 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at85 : Not (AssociativeTheory85 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3264

theorem not_model9_at86 : Not (AssociativeTheory86 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at87 : Not (AssociativeTheory87 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3260

theorem not_model9_at88 : Not (AssociativeTheory88 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at89 : Not (AssociativeTheory89 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at90 : Not (AssociativeTheory90 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at91 : Not (AssociativeTheory91 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at92 : Not (AssociativeTheory92 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at93 : Not (AssociativeTheory93 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at94 : Not (AssociativeTheory94 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3271

theorem not_model9_at95 : Not (AssociativeTheory95 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3274

theorem not_model9_at96 : Not (AssociativeTheory96 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3264

theorem not_model9_at97 : Not (AssociativeTheory97 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3278

theorem not_model9_at98 : Not (AssociativeTheory98 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3292

theorem not_model9_at99 : Not (AssociativeTheory99 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3264

theorem not_model9_at100 : Not (AssociativeTheory100 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3274

theorem not_model9_at101 : Not (AssociativeTheory101 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3264

theorem not_model9_at102 : Not (AssociativeTheory102 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3300

theorem not_model9_at103 : Not (AssociativeTheory103 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem model9_at104 : AssociativeTheory104 (Fin 3) :=
  ⟨model9_eq3306, model9_eq4512⟩

theorem not_model9_at105 : Not (AssociativeTheory105 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at106 : Not (AssociativeTheory106 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at107 : Not (AssociativeTheory107 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3256

theorem not_model9_at108 : Not (AssociativeTheory108 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3261

theorem not_model9_at109 : Not (AssociativeTheory109 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3271

theorem not_model9_at110 : Not (AssociativeTheory110 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3278

theorem model9_at111 : AssociativeTheory111 (Fin 3) :=
  ⟨model9_eq3308, model9_eq4512⟩

theorem model9_at112 : AssociativeTheory112 (Fin 3) :=
  ⟨model9_eq8, model9_eq3308, model9_eq4512⟩

theorem model9_at113 : AssociativeTheory113 (Fin 3) :=
  ⟨model9_eq3315, model9_eq4512⟩

theorem model9_at114 : AssociativeTheory114 (Fin 3) :=
  ⟨model9_eq8, model9_eq3315, model9_eq4512⟩

theorem not_model9_at115 : Not (AssociativeTheory115 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3256

theorem model9_at116 : AssociativeTheory116 (Fin 3) :=
  ⟨model9_eq3306, model9_eq3315, model9_eq4512⟩

theorem model9_at117 : AssociativeTheory117 (Fin 3) :=
  ⟨model9_eq3316, model9_eq4512⟩

theorem model9_at118 : AssociativeTheory118 (Fin 3) :=
  ⟨model9_eq323, model9_eq3316, model9_eq4512⟩

theorem model9_at119 : AssociativeTheory119 (Fin 3) :=
  ⟨model9_eq326, model9_eq3316, model9_eq4512⟩

theorem model9_at120 : AssociativeTheory120 (Fin 3) :=
  ⟨model9_eq3319, model9_eq4512⟩

theorem model9_at121 : AssociativeTheory121 (Fin 3) :=
  ⟨model9_eq3306, model9_eq3319, model9_eq4512⟩

theorem not_model9_at122 : Not (AssociativeTheory122 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3346

theorem not_model9_at123 : Not (AssociativeTheory123 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3346

theorem not_model9_at124 : Not (AssociativeTheory124 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3353

theorem not_model9_at125 : Not (AssociativeTheory125 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3353

theorem not_model9_at126 : Not (AssociativeTheory126 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3353

theorem not_model9_at127 : Not (AssociativeTheory127 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at128 : Not (AssociativeTheory128 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at129 : Not (AssociativeTheory129 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at130 : Not (AssociativeTheory130 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at131 : Not (AssociativeTheory131 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at132 : Not (AssociativeTheory132 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at133 : Not (AssociativeTheory133 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at134 : Not (AssociativeTheory134 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at135 : Not (AssociativeTheory135 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at136 : Not (AssociativeTheory136 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4271

theorem not_model9_at137 : Not (AssociativeTheory137 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at138 : Not (AssociativeTheory138 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4272

theorem not_model9_at139 : Not (AssociativeTheory139 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at140 : Not (AssociativeTheory140 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at141 : Not (AssociativeTheory141 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at142 : Not (AssociativeTheory142 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at143 : Not (AssociativeTheory143 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at144 : Not (AssociativeTheory144 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4271

theorem not_model9_at145 : Not (AssociativeTheory145 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4273

theorem not_model9_at146 : Not (AssociativeTheory146 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at147 : Not (AssociativeTheory147 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at148 : Not (AssociativeTheory148 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at149 : Not (AssociativeTheory149 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at150 : Not (AssociativeTheory150 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4275

theorem not_model9_at151 : Not (AssociativeTheory151 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at152 : Not (AssociativeTheory152 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at153 : Not (AssociativeTheory153 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at154 : Not (AssociativeTheory154 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4272

theorem not_model9_at155 : Not (AssociativeTheory155 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at156 : Not (AssociativeTheory156 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4273

theorem not_model9_at157 : Not (AssociativeTheory157 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at158 : Not (AssociativeTheory158 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at159 : Not (AssociativeTheory159 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at160 : Not (AssociativeTheory160 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4278

theorem model9_at161 : AssociativeTheory161 (Fin 3) :=
  ⟨model9_eq4283, model9_eq4512⟩

theorem model9_at162 : AssociativeTheory162 (Fin 3) :=
  ⟨model9_eq47, model9_eq4283, model9_eq4512⟩

theorem not_model9_at163 : Not (AssociativeTheory163 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq56

theorem model9_at164 : AssociativeTheory164 (Fin 3) :=
  ⟨model9_eq307, model9_eq4283, model9_eq4512⟩

theorem model9_at165 : AssociativeTheory165 (Fin 3) :=
  ⟨model9_eq326, model9_eq4283, model9_eq4512⟩

theorem model9_at166 : AssociativeTheory166 (Fin 3) :=
  ⟨model9_eq411, model9_eq4283, model9_eq4512⟩

theorem not_model9_at167 : Not (AssociativeTheory167 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq440

theorem model9_at168 : AssociativeTheory168 (Fin 3) :=
  ⟨model9_eq3253, model9_eq4283, model9_eq4512⟩

theorem not_model9_at169 : Not (AssociativeTheory169 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3256

theorem model9_at170 : AssociativeTheory170 (Fin 3) :=
  ⟨model9_eq3319, model9_eq4283, model9_eq4512⟩

theorem not_model9_at171 : Not (AssociativeTheory171 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at172 : Not (AssociativeTheory172 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4272

theorem not_model9_at173 : Not (AssociativeTheory173 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem model9_at174 : AssociativeTheory174 (Fin 3) :=
  ⟨model9_eq4284, model9_eq4512⟩

theorem not_model9_at175 : Not (AssociativeTheory175 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem model9_at176 : AssociativeTheory176 (Fin 3) :=
  ⟨model9_eq307, model9_eq4284, model9_eq4512⟩

theorem not_model9_at177 : Not (AssociativeTheory177 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem not_model9_at178 : Not (AssociativeTheory178 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at179 : Not (AssociativeTheory179 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4273

theorem not_model9_at180 : Not (AssociativeTheory180 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at181 : Not (AssociativeTheory181 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq43

theorem model9_at182 : AssociativeTheory182 (Fin 3) :=
  ⟨model9_eq4283, model9_eq4284, model9_eq4512⟩

theorem model9_at183 : AssociativeTheory183 (Fin 3) :=
  ⟨model9_eq307, model9_eq4283, model9_eq4284, model9_eq4512⟩

theorem not_model9_at184 : Not (AssociativeTheory184 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at185 : Not (AssociativeTheory185 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4287

theorem not_model9_at186 : Not (AssociativeTheory186 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4287

theorem not_model9_at187 : Not (AssociativeTheory187 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at188 : Not (AssociativeTheory188 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at189 : Not (AssociativeTheory189 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at190 : Not (AssociativeTheory190 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at191 : Not (AssociativeTheory191 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at192 : Not (AssociativeTheory192 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4273

theorem not_model9_at193 : Not (AssociativeTheory193 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at194 : Not (AssociativeTheory194 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at195 : Not (AssociativeTheory195 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at196 : Not (AssociativeTheory196 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at197 : Not (AssociativeTheory197 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at198 : Not (AssociativeTheory198 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at199 : Not (AssociativeTheory199 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at200 : Not (AssociativeTheory200 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at201 : Not (AssociativeTheory201 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at202 : Not (AssociativeTheory202 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at203 : Not (AssociativeTheory203 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at204 : Not (AssociativeTheory204 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at205 : Not (AssociativeTheory205 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at206 : Not (AssociativeTheory206 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at207 : Not (AssociativeTheory207 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq312

theorem not_model9_at208 : Not (AssociativeTheory208 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at209 : Not (AssociativeTheory209 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at210 : Not (AssociativeTheory210 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4272

theorem not_model9_at211 : Not (AssociativeTheory211 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at212 : Not (AssociativeTheory212 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at213 : Not (AssociativeTheory213 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at214 : Not (AssociativeTheory214 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at215 : Not (AssociativeTheory215 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at216 : Not (AssociativeTheory216 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at217 : Not (AssociativeTheory217 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at218 : Not (AssociativeTheory218 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at219 : Not (AssociativeTheory219 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at220 : Not (AssociativeTheory220 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at221 : Not (AssociativeTheory221 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at222 : Not (AssociativeTheory222 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at223 : Not (AssociativeTheory223 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at224 : Not (AssociativeTheory224 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at225 : Not (AssociativeTheory225 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at226 : Not (AssociativeTheory226 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at227 : Not (AssociativeTheory227 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at228 : Not (AssociativeTheory228 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4300

theorem not_model9_at229 : Not (AssociativeTheory229 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4300

theorem model9_at230 : AssociativeTheory230 (Fin 3) :=
  ⟨model9_eq4314, model9_eq4512⟩

theorem model9_at231 : AssociativeTheory231 (Fin 3) :=
  ⟨model9_eq307, model9_eq4314, model9_eq4512⟩

theorem not_model9_at232 : Not (AssociativeTheory232 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq308

theorem model9_at233 : AssociativeTheory233 (Fin 3) :=
  ⟨model9_eq323, model9_eq4314, model9_eq4512⟩

theorem not_model9_at234 : Not (AssociativeTheory234 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at235 : Not (AssociativeTheory235 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4275

theorem not_model9_at236 : Not (AssociativeTheory236 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at237 : Not (AssociativeTheory237 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at238 : Not (AssociativeTheory238 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at239 : Not (AssociativeTheory239 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4315

theorem not_model9_at240 : Not (AssociativeTheory240 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4315

theorem not_model9_at241 : Not (AssociativeTheory241 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at242 : Not (AssociativeTheory242 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at243 : Not (AssociativeTheory243 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq75

theorem not_model9_at244 : Not (AssociativeTheory244 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at245 : Not (AssociativeTheory245 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at246 : Not (AssociativeTheory246 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at247 : Not (AssociativeTheory247 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq513

theorem not_model9_at248 : Not (AssociativeTheory248 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at249 : Not (AssociativeTheory249 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3261

theorem not_model9_at250 : Not (AssociativeTheory250 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at251 : Not (AssociativeTheory251 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at252 : Not (AssociativeTheory252 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4275

theorem not_model9_at253 : Not (AssociativeTheory253 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at254 : Not (AssociativeTheory254 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at255 : Not (AssociativeTheory255 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at256 : Not (AssociativeTheory256 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at257 : Not (AssociativeTheory257 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at258 : Not (AssociativeTheory258 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4320

theorem not_model9_at259 : Not (AssociativeTheory259 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at260 : Not (AssociativeTheory260 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at261 : Not (AssociativeTheory261 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at262 : Not (AssociativeTheory262 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at263 : Not (AssociativeTheory263 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at264 : Not (AssociativeTheory264 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at265 : Not (AssociativeTheory265 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at266 : Not (AssociativeTheory266 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3260

theorem not_model9_at267 : Not (AssociativeTheory267 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3265

theorem not_model9_at268 : Not (AssociativeTheory268 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3260

theorem not_model9_at269 : Not (AssociativeTheory269 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at270 : Not (AssociativeTheory270 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at271 : Not (AssociativeTheory271 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at272 : Not (AssociativeTheory272 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at273 : Not (AssociativeTheory273 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at274 : Not (AssociativeTheory274 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at275 : Not (AssociativeTheory275 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at276 : Not (AssociativeTheory276 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at277 : Not (AssociativeTheory277 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at278 : Not (AssociativeTheory278 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at279 : Not (AssociativeTheory279 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at280 : Not (AssociativeTheory280 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at281 : Not (AssociativeTheory281 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at282 : Not (AssociativeTheory282 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at283 : Not (AssociativeTheory283 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at284 : Not (AssociativeTheory284 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at285 : Not (AssociativeTheory285 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4343

theorem not_model9_at286 : Not (AssociativeTheory286 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4343

theorem not_model9_at287 : Not (AssociativeTheory287 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at288 : Not (AssociativeTheory288 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at289 : Not (AssociativeTheory289 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at290 : Not (AssociativeTheory290 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at291 : Not (AssociativeTheory291 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4343

theorem not_model9_at292 : Not (AssociativeTheory292 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at293 : Not (AssociativeTheory293 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at294 : Not (AssociativeTheory294 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at295 : Not (AssociativeTheory295 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at296 : Not (AssociativeTheory296 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at297 : Not (AssociativeTheory297 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at298 : Not (AssociativeTheory298 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at299 : Not (AssociativeTheory299 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at300 : Not (AssociativeTheory300 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at301 : Not (AssociativeTheory301 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at302 : Not (AssociativeTheory302 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at303 : Not (AssociativeTheory303 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at304 : Not (AssociativeTheory304 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at305 : Not (AssociativeTheory305 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at306 : Not (AssociativeTheory306 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at307 : Not (AssociativeTheory307 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at308 : Not (AssociativeTheory308 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at309 : Not (AssociativeTheory309 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at310 : Not (AssociativeTheory310 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at311 : Not (AssociativeTheory311 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at312 : Not (AssociativeTheory312 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at313 : Not (AssociativeTheory313 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq308

theorem not_model9_at314 : Not (AssociativeTheory314 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at315 : Not (AssociativeTheory315 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at316 : Not (AssociativeTheory316 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at317 : Not (AssociativeTheory317 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at318 : Not (AssociativeTheory318 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3256

theorem not_model9_at319 : Not (AssociativeTheory319 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at320 : Not (AssociativeTheory320 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at321 : Not (AssociativeTheory321 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at322 : Not (AssociativeTheory322 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at323 : Not (AssociativeTheory323 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at324 : Not (AssociativeTheory324 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at325 : Not (AssociativeTheory325 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at326 : Not (AssociativeTheory326 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4272

theorem not_model9_at327 : Not (AssociativeTheory327 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at328 : Not (AssociativeTheory328 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4273

theorem not_model9_at329 : Not (AssociativeTheory329 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at330 : Not (AssociativeTheory330 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at331 : Not (AssociativeTheory331 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at332 : Not (AssociativeTheory332 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at333 : Not (AssociativeTheory333 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at334 : Not (AssociativeTheory334 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at335 : Not (AssociativeTheory335 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at336 : Not (AssociativeTheory336 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at337 : Not (AssociativeTheory337 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at338 : Not (AssociativeTheory338 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at339 : Not (AssociativeTheory339 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at340 : Not (AssociativeTheory340 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4290

theorem not_model9_at341 : Not (AssociativeTheory341 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at342 : Not (AssociativeTheory342 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at343 : Not (AssociativeTheory343 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at344 : Not (AssociativeTheory344 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at345 : Not (AssociativeTheory345 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at346 : Not (AssociativeTheory346 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4343

theorem not_model9_at347 : Not (AssociativeTheory347 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at348 : Not (AssociativeTheory348 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at349 : Not (AssociativeTheory349 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at350 : Not (AssociativeTheory350 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at351 : Not (AssociativeTheory351 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at352 : Not (AssociativeTheory352 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at353 : Not (AssociativeTheory353 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at354 : Not (AssociativeTheory354 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at355 : Not (AssociativeTheory355 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at356 : Not (AssociativeTheory356 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at357 : Not (AssociativeTheory357 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at358 : Not (AssociativeTheory358 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at359 : Not (AssociativeTheory359 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at360 : Not (AssociativeTheory360 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at361 : Not (AssociativeTheory361 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at362 : Not (AssociativeTheory362 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at363 : Not (AssociativeTheory363 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3261

theorem not_model9_at364 : Not (AssociativeTheory364 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at365 : Not (AssociativeTheory365 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3300

theorem not_model9_at366 : Not (AssociativeTheory366 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at367 : Not (AssociativeTheory367 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at368 : Not (AssociativeTheory368 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at369 : Not (AssociativeTheory369 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at370 : Not (AssociativeTheory370 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at371 : Not (AssociativeTheory371 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at372 : Not (AssociativeTheory372 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at373 : Not (AssociativeTheory373 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4275

theorem not_model9_at374 : Not (AssociativeTheory374 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at375 : Not (AssociativeTheory375 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at376 : Not (AssociativeTheory376 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at377 : Not (AssociativeTheory377 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at378 : Not (AssociativeTheory378 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at379 : Not (AssociativeTheory379 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at380 : Not (AssociativeTheory380 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at381 : Not (AssociativeTheory381 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at382 : Not (AssociativeTheory382 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at383 : Not (AssociativeTheory383 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at384 : Not (AssociativeTheory384 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at385 : Not (AssociativeTheory385 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at386 : Not (AssociativeTheory386 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at387 : Not (AssociativeTheory387 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at388 : Not (AssociativeTheory388 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at389 : Not (AssociativeTheory389 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at390 : Not (AssociativeTheory390 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at391 : Not (AssociativeTheory391 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4362

theorem not_model9_at392 : Not (AssociativeTheory392 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at393 : Not (AssociativeTheory393 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at394 : Not (AssociativeTheory394 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4293

theorem not_model9_at395 : Not (AssociativeTheory395 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at396 : Not (AssociativeTheory396 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at397 : Not (AssociativeTheory397 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at398 : Not (AssociativeTheory398 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at399 : Not (AssociativeTheory399 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at400 : Not (AssociativeTheory400 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at401 : Not (AssociativeTheory401 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at402 : Not (AssociativeTheory402 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at403 : Not (AssociativeTheory403 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at404 : Not (AssociativeTheory404 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at405 : Not (AssociativeTheory405 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at406 : Not (AssociativeTheory406 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4358

theorem not_model9_at407 : Not (AssociativeTheory407 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at408 : Not (AssociativeTheory408 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4364

theorem not_model9_at409 : Not (AssociativeTheory409 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at410 : Not (AssociativeTheory410 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4364

theorem not_model9_at411 : Not (AssociativeTheory411 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at412 : Not (AssociativeTheory412 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4364

theorem not_model9_at413 : Not (AssociativeTheory413 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at414 : Not (AssociativeTheory414 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at415 : Not (AssociativeTheory415 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at416 : Not (AssociativeTheory416 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at417 : Not (AssociativeTheory417 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4364

theorem not_model9_at418 : Not (AssociativeTheory418 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4364

theorem not_model9_at419 : Not (AssociativeTheory419 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at420 : Not (AssociativeTheory420 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at421 : Not (AssociativeTheory421 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at422 : Not (AssociativeTheory422 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at423 : Not (AssociativeTheory423 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at424 : Not (AssociativeTheory424 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at425 : Not (AssociativeTheory425 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at426 : Not (AssociativeTheory426 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at427 : Not (AssociativeTheory427 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq309

theorem not_model9_at428 : Not (AssociativeTheory428 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at429 : Not (AssociativeTheory429 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at430 : Not (AssociativeTheory430 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at431 : Not (AssociativeTheory431 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at432 : Not (AssociativeTheory432 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4273

theorem not_model9_at433 : Not (AssociativeTheory433 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at434 : Not (AssociativeTheory434 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4270

theorem not_model9_at435 : Not (AssociativeTheory435 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at436 : Not (AssociativeTheory436 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at437 : Not (AssociativeTheory437 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at438 : Not (AssociativeTheory438 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at439 : Not (AssociativeTheory439 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at440 : Not (AssociativeTheory440 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at441 : Not (AssociativeTheory441 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at442 : Not (AssociativeTheory442 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4269

theorem not_model9_at443 : Not (AssociativeTheory443 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at444 : Not (AssociativeTheory444 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at445 : Not (AssociativeTheory445 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4369

theorem not_model9_at446 : Not (AssociativeTheory446 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at447 : Not (AssociativeTheory447 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4291

theorem not_model9_at448 : Not (AssociativeTheory448 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at449 : Not (AssociativeTheory449 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at450 : Not (AssociativeTheory450 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq40

theorem not_model9_at451 : Not (AssociativeTheory451 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at452 : Not (AssociativeTheory452 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq3267

theorem not_model9_at453 : Not (AssociativeTheory453 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4268

theorem not_model9_at454 : Not (AssociativeTheory454 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276

theorem not_model9_at455 : Not (AssociativeTheory455 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4321

theorem not_model9_at456 : Not (AssociativeTheory456 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model9_eq4276
