import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model4_op := finOpTable "[[0,1],[0,1]]"
private def model4 : Magma (Fin 2) where op := model4_op
private instance : Magma (Fin 2) := model4

private theorem model4_eq1 : Equation1 (Fin 2) := by decideFin!
private theorem not_model4_eq2 : Not (Equation2 (Fin 2)) := by decideFin!
private theorem model4_eq3 : Equation3 (Fin 2) := by decideFin!
private theorem not_model4_eq4 : Not (Equation4 (Fin 2)) := by decideFin!
private theorem model4_eq5 : Equation5 (Fin 2) := by decideFin!
private theorem model4_eq8 : Equation8 (Fin 2) := by decideFin!
private theorem model4_eq10 : Equation10 (Fin 2) := by decideFin!
private theorem not_model4_eq11 : Not (Equation11 (Fin 2)) := by decideFin!
private theorem not_model4_eq14 : Not (Equation14 (Fin 2)) := by decideFin!
private theorem model4_eq16 : Equation16 (Fin 2) := by decideFin!
private theorem not_model4_eq38 : Not (Equation38 (Fin 2)) := by decideFin!
private theorem model4_eq39 : Equation39 (Fin 2) := by decideFin!
private theorem not_model4_eq40 : Not (Equation40 (Fin 2)) := by decideFin!
private theorem not_model4_eq41 : Not (Equation41 (Fin 2)) := by decideFin!
private theorem not_model4_eq43 : Not (Equation43 (Fin 2)) := by decideFin!
private theorem model4_eq47 : Equation47 (Fin 2) := by decideFin!
private theorem not_model4_eq56 : Not (Equation56 (Fin 2)) := by decideFin!
private theorem not_model4_eq66 : Not (Equation66 (Fin 2)) := by decideFin!
private theorem model4_eq75 : Equation75 (Fin 2) := by decideFin!
private theorem model4_eq307 : Equation307 (Fin 2) := by decideFin!
private theorem not_model4_eq308 : Not (Equation308 (Fin 2)) := by decideFin!
private theorem model4_eq309 : Equation309 (Fin 2) := by decideFin!
private theorem not_model4_eq310 : Not (Equation310 (Fin 2)) := by decideFin!
private theorem not_model4_eq311 : Not (Equation311 (Fin 2)) := by decideFin!
private theorem model4_eq312 : Equation312 (Fin 2) := by decideFin!
private theorem not_model4_eq313 : Not (Equation313 (Fin 2)) := by decideFin!
private theorem not_model4_eq314 : Not (Equation314 (Fin 2)) := by decideFin!
private theorem model4_eq315 : Equation315 (Fin 2) := by decideFin!
private theorem not_model4_eq316 : Not (Equation316 (Fin 2)) := by decideFin!
private theorem model4_eq318 : Equation318 (Fin 2) := by decideFin!
private theorem model4_eq323 : Equation323 (Fin 2) := by decideFin!
private theorem not_model4_eq325 : Not (Equation325 (Fin 2)) := by decideFin!
private theorem model4_eq326 : Equation326 (Fin 2) := by decideFin!
private theorem not_model4_eq327 : Not (Equation327 (Fin 2)) := by decideFin!
private theorem model4_eq329 : Equation329 (Fin 2) := by decideFin!
private theorem not_model4_eq332 : Not (Equation332 (Fin 2)) := by decideFin!
private theorem model4_eq333 : Equation333 (Fin 2) := by decideFin!
private theorem model4_eq343 : Equation343 (Fin 2) := by decideFin!
private theorem model4_eq411 : Equation411 (Fin 2) := by decideFin!
private theorem model4_eq419 : Equation419 (Fin 2) := by decideFin!
private theorem model4_eq429 : Equation429 (Fin 2) := by decideFin!
private theorem not_model4_eq440 : Not (Equation440 (Fin 2)) := by decideFin!
private theorem not_model4_eq477 : Not (Equation477 (Fin 2)) := by decideFin!
private theorem not_model4_eq504 : Not (Equation504 (Fin 2)) := by decideFin!
private theorem model4_eq513 : Equation513 (Fin 2) := by decideFin!
private theorem model4_eq3253 : Equation3253 (Fin 2) := by decideFin!
private theorem model4_eq3255 : Equation3255 (Fin 2) := by decideFin!
private theorem not_model4_eq3256 : Not (Equation3256 (Fin 2)) := by decideFin!
private theorem model4_eq3258 : Equation3258 (Fin 2) := by decideFin!
private theorem not_model4_eq3259 : Not (Equation3259 (Fin 2)) := by decideFin!
private theorem not_model4_eq3260 : Not (Equation3260 (Fin 2)) := by decideFin!
private theorem model4_eq3261 : Equation3261 (Fin 2) := by decideFin!
private theorem model4_eq3264 : Equation3264 (Fin 2) := by decideFin!
private theorem not_model4_eq3265 : Not (Equation3265 (Fin 2)) := by decideFin!
private theorem not_model4_eq3267 : Not (Equation3267 (Fin 2)) := by decideFin!
private theorem model4_eq3271 : Equation3271 (Fin 2) := by decideFin!
private theorem not_model4_eq3273 : Not (Equation3273 (Fin 2)) := by decideFin!
private theorem model4_eq3274 : Equation3274 (Fin 2) := by decideFin!
private theorem not_model4_eq3275 : Not (Equation3275 (Fin 2)) := by decideFin!
private theorem not_model4_eq3277 : Not (Equation3277 (Fin 2)) := by decideFin!
private theorem model4_eq3278 : Equation3278 (Fin 2) := by decideFin!
private theorem not_model4_eq3290 : Not (Equation3290 (Fin 2)) := by decideFin!
private theorem model4_eq3292 : Equation3292 (Fin 2) := by decideFin!
private theorem model4_eq3300 : Equation3300 (Fin 2) := by decideFin!
private theorem model4_eq3306 : Equation3306 (Fin 2) := by decideFin!
private theorem not_model4_eq3308 : Not (Equation3308 (Fin 2)) := by decideFin!
private theorem model4_eq3309 : Equation3309 (Fin 2) := by decideFin!
private theorem not_model4_eq3315 : Not (Equation3315 (Fin 2)) := by decideFin!
private theorem model4_eq3316 : Equation3316 (Fin 2) := by decideFin!
private theorem model4_eq3319 : Equation3319 (Fin 2) := by decideFin!
private theorem model4_eq3322 : Equation3322 (Fin 2) := by decideFin!
private theorem not_model4_eq3323 : Not (Equation3323 (Fin 2)) := by decideFin!
private theorem model4_eq3326 : Equation3326 (Fin 2) := by decideFin!
private theorem not_model4_eq3331 : Not (Equation3331 (Fin 2)) := by decideFin!
private theorem model4_eq3334 : Equation3334 (Fin 2) := by decideFin!
private theorem not_model4_eq3342 : Not (Equation3342 (Fin 2)) := by decideFin!
private theorem model4_eq3346 : Equation3346 (Fin 2) := by decideFin!
private theorem not_model4_eq3350 : Not (Equation3350 (Fin 2)) := by decideFin!
private theorem model4_eq3353 : Equation3353 (Fin 2) := by decideFin!
private theorem model4_eq3388 : Equation3388 (Fin 2) := by decideFin!
private theorem model4_eq3414 : Equation3414 (Fin 2) := by decideFin!
private theorem not_model4_eq4268 : Not (Equation4268 (Fin 2)) := by decideFin!
private theorem model4_eq4269 : Equation4269 (Fin 2) := by decideFin!
private theorem not_model4_eq4270 : Not (Equation4270 (Fin 2)) := by decideFin!
private theorem not_model4_eq4271 : Not (Equation4271 (Fin 2)) := by decideFin!
private theorem model4_eq4272 : Equation4272 (Fin 2) := by decideFin!
private theorem not_model4_eq4273 : Not (Equation4273 (Fin 2)) := by decideFin!
private theorem not_model4_eq4274 : Not (Equation4274 (Fin 2)) := by decideFin!
private theorem model4_eq4275 : Equation4275 (Fin 2) := by decideFin!
private theorem not_model4_eq4276 : Not (Equation4276 (Fin 2)) := by decideFin!
private theorem not_model4_eq4277 : Not (Equation4277 (Fin 2)) := by decideFin!
private theorem model4_eq4278 : Equation4278 (Fin 2) := by decideFin!
private theorem not_model4_eq4279 : Not (Equation4279 (Fin 2)) := by decideFin!
private theorem not_model4_eq4280 : Not (Equation4280 (Fin 2)) := by decideFin!
private theorem not_model4_eq4283 : Not (Equation4283 (Fin 2)) := by decideFin!
private theorem model4_eq4284 : Equation4284 (Fin 2) := by decideFin!
private theorem not_model4_eq4286 : Not (Equation4286 (Fin 2)) := by decideFin!
private theorem model4_eq4287 : Equation4287 (Fin 2) := by decideFin!
private theorem not_model4_eq4288 : Not (Equation4288 (Fin 2)) := by decideFin!
private theorem not_model4_eq4290 : Not (Equation4290 (Fin 2)) := by decideFin!
private theorem model4_eq4291 : Equation4291 (Fin 2) := by decideFin!
private theorem not_model4_eq4293 : Not (Equation4293 (Fin 2)) := by decideFin!
private theorem model4_eq4296 : Equation4296 (Fin 2) := by decideFin!
private theorem not_model4_eq4297 : Not (Equation4297 (Fin 2)) := by decideFin!
private theorem not_model4_eq4299 : Not (Equation4299 (Fin 2)) := by decideFin!
private theorem model4_eq4300 : Equation4300 (Fin 2) := by decideFin!
private theorem not_model4_eq4301 : Not (Equation4301 (Fin 2)) := by decideFin!
private theorem model4_eq4304 : Equation4304 (Fin 2) := by decideFin!
private theorem not_model4_eq4305 : Not (Equation4305 (Fin 2)) := by decideFin!
private theorem not_model4_eq4314 : Not (Equation4314 (Fin 2)) := by decideFin!
private theorem not_model4_eq4315 : Not (Equation4315 (Fin 2)) := by decideFin!
private theorem not_model4_eq4318 : Not (Equation4318 (Fin 2)) := by decideFin!
private theorem model4_eq4320 : Equation4320 (Fin 2) := by decideFin!
private theorem not_model4_eq4321 : Not (Equation4321 (Fin 2)) := by decideFin!
private theorem not_model4_eq4325 : Not (Equation4325 (Fin 2)) := by decideFin!
private theorem model4_eq4327 : Equation4327 (Fin 2) := by decideFin!
private theorem not_model4_eq4331 : Not (Equation4331 (Fin 2)) := by decideFin!
private theorem not_model4_eq4343 : Not (Equation4343 (Fin 2)) := by decideFin!
private theorem not_model4_eq4358 : Not (Equation4358 (Fin 2)) := by decideFin!
private theorem model4_eq4362 : Equation4362 (Fin 2) := by decideFin!
private theorem not_model4_eq4364 : Not (Equation4364 (Fin 2)) := by decideFin!
private theorem not_model4_eq4369 : Not (Equation4369 (Fin 2)) := by decideFin!
private theorem model4_eq4512 : Equation4512 (Fin 2) := by decideFin!

theorem model4_at1 : AssociativeTheory1 (Fin 2) :=
  model4_eq4512

theorem not_model4_at2 : Not (AssociativeTheory2 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq2

theorem model4_at3 : AssociativeTheory3 (Fin 2) :=
  ⟨model4_eq3, model4_eq4512⟩

theorem not_model4_at4 : Not (AssociativeTheory4 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4

theorem model4_at5 : AssociativeTheory5 (Fin 2) :=
  ⟨model4_eq5, model4_eq4512⟩

theorem model4_at6 : AssociativeTheory6 (Fin 2) :=
  ⟨model4_eq8, model4_eq4512⟩

theorem model4_at7 : AssociativeTheory7 (Fin 2) :=
  ⟨model4_eq10, model4_eq4512⟩

theorem not_model4_at8 : Not (AssociativeTheory8 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq11

theorem not_model4_at9 : Not (AssociativeTheory9 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq14

theorem model4_at10 : AssociativeTheory10 (Fin 2) :=
  ⟨model4_eq16, model4_eq4512⟩

theorem not_model4_at11 : Not (AssociativeTheory11 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq38

theorem model4_at12 : AssociativeTheory12 (Fin 2) :=
  ⟨model4_eq39, model4_eq4512⟩

theorem not_model4_at13 : Not (AssociativeTheory13 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq38

theorem not_model4_at14 : Not (AssociativeTheory14 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at15 : Not (AssociativeTheory15 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at16 : Not (AssociativeTheory16 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at17 : Not (AssociativeTheory17 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at18 : Not (AssociativeTheory18 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem model4_at19 : AssociativeTheory19 (Fin 2) :=
  ⟨model4_eq47, model4_eq4512⟩

theorem not_model4_at20 : Not (AssociativeTheory20 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at21 : Not (AssociativeTheory21 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq56

theorem not_model4_at22 : Not (AssociativeTheory22 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at23 : AssociativeTheory23 (Fin 2) :=
  ⟨model4_eq75, model4_eq4512⟩

theorem not_model4_at24 : Not (AssociativeTheory24 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq56

theorem model4_at25 : AssociativeTheory25 (Fin 2) :=
  ⟨model4_eq307, model4_eq4512⟩

theorem not_model4_at26 : Not (AssociativeTheory26 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at27 : Not (AssociativeTheory27 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at28 : Not (AssociativeTheory28 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at29 : Not (AssociativeTheory29 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq308

theorem model4_at30 : AssociativeTheory30 (Fin 2) :=
  ⟨model4_eq309, model4_eq4512⟩

theorem not_model4_at31 : Not (AssociativeTheory31 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at32 : Not (AssociativeTheory32 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq308

theorem not_model4_at33 : Not (AssociativeTheory33 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq310

theorem not_model4_at34 : Not (AssociativeTheory34 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq311

theorem not_model4_at35 : Not (AssociativeTheory35 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at36 : Not (AssociativeTheory36 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at37 : AssociativeTheory37 (Fin 2) :=
  ⟨model4_eq312, model4_eq4512⟩

theorem model4_at38 : AssociativeTheory38 (Fin 2) :=
  ⟨model4_eq309, model4_eq312, model4_eq4512⟩

theorem model4_at39 : AssociativeTheory39 (Fin 2) :=
  ⟨model4_eq315, model4_eq4512⟩

theorem model4_at40 : AssociativeTheory40 (Fin 2) :=
  ⟨model4_eq318, model4_eq4512⟩

theorem model4_at41 : AssociativeTheory41 (Fin 2) :=
  ⟨model4_eq323, model4_eq4512⟩

theorem not_model4_at42 : Not (AssociativeTheory42 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at43 : AssociativeTheory43 (Fin 2) :=
  ⟨model4_eq309, model4_eq323, model4_eq4512⟩

theorem model4_at44 : AssociativeTheory44 (Fin 2) :=
  ⟨model4_eq312, model4_eq323, model4_eq4512⟩

theorem not_model4_at45 : Not (AssociativeTheory45 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq325

theorem not_model4_at46 : Not (AssociativeTheory46 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq325

theorem not_model4_at47 : Not (AssociativeTheory47 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq308

theorem not_model4_at48 : Not (AssociativeTheory48 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq325

theorem model4_at49 : AssociativeTheory49 (Fin 2) :=
  ⟨model4_eq326, model4_eq4512⟩

theorem model4_at50 : AssociativeTheory50 (Fin 2) :=
  ⟨model4_eq323, model4_eq326, model4_eq4512⟩

theorem model4_at51 : AssociativeTheory51 (Fin 2) :=
  ⟨model4_eq333, model4_eq4512⟩

theorem model4_at52 : AssociativeTheory52 (Fin 2) :=
  ⟨model4_eq3, model4_eq333, model4_eq4512⟩

theorem model4_at53 : AssociativeTheory53 (Fin 2) :=
  ⟨model4_eq326, model4_eq333, model4_eq4512⟩

theorem model4_at54 : AssociativeTheory54 (Fin 2) :=
  ⟨model4_eq411, model4_eq4512⟩

theorem not_model4_at55 : Not (AssociativeTheory55 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at56 : AssociativeTheory56 (Fin 2) :=
  ⟨model4_eq419, model4_eq4512⟩

theorem model4_at57 : AssociativeTheory57 (Fin 2) :=
  ⟨model4_eq429, model4_eq4512⟩

theorem not_model4_at58 : Not (AssociativeTheory58 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq440

theorem not_model4_at59 : Not (AssociativeTheory59 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at60 : Not (AssociativeTheory60 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq504

theorem model4_at61 : AssociativeTheory61 (Fin 2) :=
  ⟨model4_eq513, model4_eq4512⟩

theorem not_model4_at62 : Not (AssociativeTheory62 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq440

theorem model4_at63 : AssociativeTheory63 (Fin 2) :=
  ⟨model4_eq3253, model4_eq4512⟩

theorem not_model4_at64 : Not (AssociativeTheory64 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at65 : AssociativeTheory65 (Fin 2) :=
  ⟨model4_eq3255, model4_eq4512⟩

theorem model4_at66 : AssociativeTheory66 (Fin 2) :=
  ⟨model4_eq326, model4_eq3255, model4_eq4512⟩

theorem not_model4_at67 : Not (AssociativeTheory67 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3256

theorem model4_at68 : AssociativeTheory68 (Fin 2) :=
  ⟨model4_eq3258, model4_eq4512⟩

theorem model4_at69 : AssociativeTheory69 (Fin 2) :=
  ⟨model4_eq323, model4_eq3258, model4_eq4512⟩

theorem model4_at70 : AssociativeTheory70 (Fin 2) :=
  ⟨model4_eq3255, model4_eq3258, model4_eq4512⟩

theorem not_model4_at71 : Not (AssociativeTheory71 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3259

theorem not_model4_at72 : Not (AssociativeTheory72 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3260

theorem not_model4_at73 : Not (AssociativeTheory73 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem model4_at74 : AssociativeTheory74 (Fin 2) :=
  ⟨model4_eq3261, model4_eq4512⟩

theorem model4_at75 : AssociativeTheory75 (Fin 2) :=
  ⟨model4_eq3264, model4_eq4512⟩

theorem not_model4_at76 : Not (AssociativeTheory76 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at77 : Not (AssociativeTheory77 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq308

theorem model4_at78 : AssociativeTheory78 (Fin 2) :=
  ⟨model4_eq312, model4_eq3264, model4_eq4512⟩

theorem not_model4_at79 : Not (AssociativeTheory79 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3260

theorem not_model4_at80 : Not (AssociativeTheory80 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at81 : Not (AssociativeTheory81 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3265

theorem not_model4_at82 : Not (AssociativeTheory82 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at83 : Not (AssociativeTheory83 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3260

theorem not_model4_at84 : Not (AssociativeTheory84 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at85 : Not (AssociativeTheory85 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3265

theorem not_model4_at86 : Not (AssociativeTheory86 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at87 : Not (AssociativeTheory87 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3260

theorem not_model4_at88 : Not (AssociativeTheory88 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at89 : Not (AssociativeTheory89 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at90 : Not (AssociativeTheory90 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at91 : Not (AssociativeTheory91 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at92 : Not (AssociativeTheory92 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at93 : Not (AssociativeTheory93 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem model4_at94 : AssociativeTheory94 (Fin 2) :=
  ⟨model4_eq3271, model4_eq4512⟩

theorem model4_at95 : AssociativeTheory95 (Fin 2) :=
  ⟨model4_eq3274, model4_eq4512⟩

theorem model4_at96 : AssociativeTheory96 (Fin 2) :=
  ⟨model4_eq3264, model4_eq3274, model4_eq4512⟩

theorem model4_at97 : AssociativeTheory97 (Fin 2) :=
  ⟨model4_eq3278, model4_eq4512⟩

theorem model4_at98 : AssociativeTheory98 (Fin 2) :=
  ⟨model4_eq3292, model4_eq4512⟩

theorem model4_at99 : AssociativeTheory99 (Fin 2) :=
  ⟨model4_eq3264, model4_eq3292, model4_eq4512⟩

theorem model4_at100 : AssociativeTheory100 (Fin 2) :=
  ⟨model4_eq3274, model4_eq3292, model4_eq4512⟩

theorem model4_at101 : AssociativeTheory101 (Fin 2) :=
  ⟨model4_eq3264, model4_eq3274, model4_eq3292, model4_eq4512⟩

theorem model4_at102 : AssociativeTheory102 (Fin 2) :=
  ⟨model4_eq3300, model4_eq4512⟩

theorem model4_at103 : AssociativeTheory103 (Fin 2) :=
  ⟨model4_eq309, model4_eq3300, model4_eq4512⟩

theorem model4_at104 : AssociativeTheory104 (Fin 2) :=
  ⟨model4_eq3306, model4_eq4512⟩

theorem not_model4_at105 : Not (AssociativeTheory105 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at106 : Not (AssociativeTheory106 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at107 : Not (AssociativeTheory107 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3256

theorem model4_at108 : AssociativeTheory108 (Fin 2) :=
  ⟨model4_eq3261, model4_eq3306, model4_eq4512⟩

theorem model4_at109 : AssociativeTheory109 (Fin 2) :=
  ⟨model4_eq3271, model4_eq3306, model4_eq4512⟩

theorem model4_at110 : AssociativeTheory110 (Fin 2) :=
  ⟨model4_eq3278, model4_eq3306, model4_eq4512⟩

theorem not_model4_at111 : Not (AssociativeTheory111 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3308

theorem not_model4_at112 : Not (AssociativeTheory112 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3308

theorem not_model4_at113 : Not (AssociativeTheory113 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3315

theorem not_model4_at114 : Not (AssociativeTheory114 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3315

theorem not_model4_at115 : Not (AssociativeTheory115 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3256

theorem not_model4_at116 : Not (AssociativeTheory116 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3315

theorem model4_at117 : AssociativeTheory117 (Fin 2) :=
  ⟨model4_eq3316, model4_eq4512⟩

theorem model4_at118 : AssociativeTheory118 (Fin 2) :=
  ⟨model4_eq323, model4_eq3316, model4_eq4512⟩

theorem model4_at119 : AssociativeTheory119 (Fin 2) :=
  ⟨model4_eq326, model4_eq3316, model4_eq4512⟩

theorem model4_at120 : AssociativeTheory120 (Fin 2) :=
  ⟨model4_eq3319, model4_eq4512⟩

theorem model4_at121 : AssociativeTheory121 (Fin 2) :=
  ⟨model4_eq3306, model4_eq3319, model4_eq4512⟩

theorem model4_at122 : AssociativeTheory122 (Fin 2) :=
  ⟨model4_eq3346, model4_eq4512⟩

theorem model4_at123 : AssociativeTheory123 (Fin 2) :=
  ⟨model4_eq8, model4_eq3346, model4_eq4512⟩

theorem model4_at124 : AssociativeTheory124 (Fin 2) :=
  ⟨model4_eq3353, model4_eq4512⟩

theorem model4_at125 : AssociativeTheory125 (Fin 2) :=
  ⟨model4_eq8, model4_eq3353, model4_eq4512⟩

theorem model4_at126 : AssociativeTheory126 (Fin 2) :=
  ⟨model4_eq3319, model4_eq3353, model4_eq4512⟩

theorem not_model4_at127 : Not (AssociativeTheory127 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at128 : Not (AssociativeTheory128 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at129 : AssociativeTheory129 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4512⟩

theorem not_model4_at130 : Not (AssociativeTheory130 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at131 : Not (AssociativeTheory131 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at132 : Not (AssociativeTheory132 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at133 : Not (AssociativeTheory133 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at134 : Not (AssociativeTheory134 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at135 : Not (AssociativeTheory135 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at136 : Not (AssociativeTheory136 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4271

theorem not_model4_at137 : Not (AssociativeTheory137 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at138 : AssociativeTheory138 (Fin 2) :=
  ⟨model4_eq4272, model4_eq4512⟩

theorem not_model4_at139 : Not (AssociativeTheory139 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem model4_at140 : AssociativeTheory140 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4272, model4_eq4512⟩

theorem not_model4_at141 : Not (AssociativeTheory141 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at142 : Not (AssociativeTheory142 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at143 : Not (AssociativeTheory143 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at144 : Not (AssociativeTheory144 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4271

theorem not_model4_at145 : Not (AssociativeTheory145 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at146 : Not (AssociativeTheory146 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at147 : Not (AssociativeTheory147 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at148 : Not (AssociativeTheory148 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at149 : Not (AssociativeTheory149 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem model4_at150 : AssociativeTheory150 (Fin 2) :=
  ⟨model4_eq4275, model4_eq4512⟩

theorem not_model4_at151 : Not (AssociativeTheory151 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem model4_at152 : AssociativeTheory152 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4275, model4_eq4512⟩

theorem not_model4_at153 : Not (AssociativeTheory153 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem model4_at154 : AssociativeTheory154 (Fin 2) :=
  ⟨model4_eq4272, model4_eq4275, model4_eq4512⟩

theorem model4_at155 : AssociativeTheory155 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4272, model4_eq4275, model4_eq4512⟩

theorem not_model4_at156 : Not (AssociativeTheory156 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at157 : Not (AssociativeTheory157 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at158 : Not (AssociativeTheory158 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at159 : Not (AssociativeTheory159 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at160 : AssociativeTheory160 (Fin 2) :=
  ⟨model4_eq4278, model4_eq4512⟩

theorem not_model4_at161 : Not (AssociativeTheory161 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at162 : Not (AssociativeTheory162 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at163 : Not (AssociativeTheory163 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq56

theorem not_model4_at164 : Not (AssociativeTheory164 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at165 : Not (AssociativeTheory165 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at166 : Not (AssociativeTheory166 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at167 : Not (AssociativeTheory167 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq440

theorem not_model4_at168 : Not (AssociativeTheory168 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at169 : Not (AssociativeTheory169 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3256

theorem not_model4_at170 : Not (AssociativeTheory170 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at171 : Not (AssociativeTheory171 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at172 : Not (AssociativeTheory172 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at173 : Not (AssociativeTheory173 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at174 : AssociativeTheory174 (Fin 2) :=
  ⟨model4_eq4284, model4_eq4512⟩

theorem not_model4_at175 : Not (AssociativeTheory175 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at176 : AssociativeTheory176 (Fin 2) :=
  ⟨model4_eq307, model4_eq4284, model4_eq4512⟩

theorem not_model4_at177 : Not (AssociativeTheory177 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem model4_at178 : AssociativeTheory178 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4284, model4_eq4512⟩

theorem not_model4_at179 : Not (AssociativeTheory179 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at180 : Not (AssociativeTheory180 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at181 : Not (AssociativeTheory181 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq43

theorem not_model4_at182 : Not (AssociativeTheory182 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at183 : Not (AssociativeTheory183 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at184 : Not (AssociativeTheory184 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at185 : AssociativeTheory185 (Fin 2) :=
  ⟨model4_eq4287, model4_eq4512⟩

theorem model4_at186 : AssociativeTheory186 (Fin 2) :=
  ⟨model4_eq307, model4_eq4287, model4_eq4512⟩

theorem not_model4_at187 : Not (AssociativeTheory187 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at188 : Not (AssociativeTheory188 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at189 : Not (AssociativeTheory189 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at190 : Not (AssociativeTheory190 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at191 : Not (AssociativeTheory191 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at192 : Not (AssociativeTheory192 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at193 : Not (AssociativeTheory193 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at194 : Not (AssociativeTheory194 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at195 : Not (AssociativeTheory195 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at196 : Not (AssociativeTheory196 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at197 : Not (AssociativeTheory197 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at198 : Not (AssociativeTheory198 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at199 : Not (AssociativeTheory199 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at200 : Not (AssociativeTheory200 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at201 : Not (AssociativeTheory201 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at202 : Not (AssociativeTheory202 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at203 : Not (AssociativeTheory203 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at204 : Not (AssociativeTheory204 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at205 : AssociativeTheory205 (Fin 2) :=
  ⟨model4_eq4291, model4_eq4512⟩

theorem model4_at206 : AssociativeTheory206 (Fin 2) :=
  ⟨model4_eq307, model4_eq4291, model4_eq4512⟩

theorem model4_at207 : AssociativeTheory207 (Fin 2) :=
  ⟨model4_eq312, model4_eq4291, model4_eq4512⟩

theorem model4_at208 : AssociativeTheory208 (Fin 2) :=
  ⟨model4_eq326, model4_eq4291, model4_eq4512⟩

theorem not_model4_at209 : Not (AssociativeTheory209 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem model4_at210 : AssociativeTheory210 (Fin 2) :=
  ⟨model4_eq4272, model4_eq4291, model4_eq4512⟩

theorem not_model4_at211 : Not (AssociativeTheory211 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at212 : Not (AssociativeTheory212 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at213 : Not (AssociativeTheory213 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at214 : Not (AssociativeTheory214 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at215 : Not (AssociativeTheory215 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at216 : Not (AssociativeTheory216 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at217 : AssociativeTheory217 (Fin 2) :=
  ⟨model4_eq4284, model4_eq4291, model4_eq4512⟩

theorem model4_at218 : AssociativeTheory218 (Fin 2) :=
  ⟨model4_eq307, model4_eq4284, model4_eq4291, model4_eq4512⟩

theorem not_model4_at219 : Not (AssociativeTheory219 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at220 : Not (AssociativeTheory220 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at221 : Not (AssociativeTheory221 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at222 : Not (AssociativeTheory222 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at223 : Not (AssociativeTheory223 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at224 : Not (AssociativeTheory224 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at225 : Not (AssociativeTheory225 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at226 : Not (AssociativeTheory226 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at227 : Not (AssociativeTheory227 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at228 : AssociativeTheory228 (Fin 2) :=
  ⟨model4_eq4300, model4_eq4512⟩

theorem model4_at229 : AssociativeTheory229 (Fin 2) :=
  ⟨model4_eq307, model4_eq4300, model4_eq4512⟩

theorem not_model4_at230 : Not (AssociativeTheory230 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at231 : Not (AssociativeTheory231 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at232 : Not (AssociativeTheory232 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq308

theorem not_model4_at233 : Not (AssociativeTheory233 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at234 : Not (AssociativeTheory234 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at235 : Not (AssociativeTheory235 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at236 : Not (AssociativeTheory236 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at237 : Not (AssociativeTheory237 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at238 : Not (AssociativeTheory238 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at239 : Not (AssociativeTheory239 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4315

theorem not_model4_at240 : Not (AssociativeTheory240 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4315

theorem model4_at241 : AssociativeTheory241 (Fin 2) :=
  ⟨model4_eq4320, model4_eq4512⟩

theorem model4_at242 : AssociativeTheory242 (Fin 2) :=
  ⟨model4_eq47, model4_eq4320, model4_eq4512⟩

theorem model4_at243 : AssociativeTheory243 (Fin 2) :=
  ⟨model4_eq75, model4_eq4320, model4_eq4512⟩

theorem model4_at244 : AssociativeTheory244 (Fin 2) :=
  ⟨model4_eq307, model4_eq4320, model4_eq4512⟩

theorem model4_at245 : AssociativeTheory245 (Fin 2) :=
  ⟨model4_eq323, model4_eq4320, model4_eq4512⟩

theorem model4_at246 : AssociativeTheory246 (Fin 2) :=
  ⟨model4_eq411, model4_eq4320, model4_eq4512⟩

theorem model4_at247 : AssociativeTheory247 (Fin 2) :=
  ⟨model4_eq513, model4_eq4320, model4_eq4512⟩

theorem model4_at248 : AssociativeTheory248 (Fin 2) :=
  ⟨model4_eq3253, model4_eq4320, model4_eq4512⟩

theorem model4_at249 : AssociativeTheory249 (Fin 2) :=
  ⟨model4_eq3261, model4_eq4320, model4_eq4512⟩

theorem model4_at250 : AssociativeTheory250 (Fin 2) :=
  ⟨model4_eq3306, model4_eq4320, model4_eq4512⟩

theorem not_model4_at251 : Not (AssociativeTheory251 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem model4_at252 : AssociativeTheory252 (Fin 2) :=
  ⟨model4_eq4275, model4_eq4320, model4_eq4512⟩

theorem not_model4_at253 : Not (AssociativeTheory253 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at254 : Not (AssociativeTheory254 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at255 : Not (AssociativeTheory255 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at256 : Not (AssociativeTheory256 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at257 : Not (AssociativeTheory257 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at258 : Not (AssociativeTheory258 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at259 : Not (AssociativeTheory259 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at260 : Not (AssociativeTheory260 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at261 : Not (AssociativeTheory261 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at262 : Not (AssociativeTheory262 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at263 : Not (AssociativeTheory263 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at264 : Not (AssociativeTheory264 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at265 : Not (AssociativeTheory265 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at266 : Not (AssociativeTheory266 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3260

theorem not_model4_at267 : Not (AssociativeTheory267 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3265

theorem not_model4_at268 : Not (AssociativeTheory268 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3260

theorem not_model4_at269 : Not (AssociativeTheory269 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at270 : Not (AssociativeTheory270 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at271 : Not (AssociativeTheory271 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at272 : Not (AssociativeTheory272 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at273 : Not (AssociativeTheory273 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at274 : Not (AssociativeTheory274 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at275 : Not (AssociativeTheory275 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at276 : Not (AssociativeTheory276 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at277 : Not (AssociativeTheory277 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at278 : Not (AssociativeTheory278 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at279 : Not (AssociativeTheory279 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at280 : Not (AssociativeTheory280 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at281 : Not (AssociativeTheory281 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at282 : Not (AssociativeTheory282 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at283 : Not (AssociativeTheory283 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at284 : Not (AssociativeTheory284 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at285 : Not (AssociativeTheory285 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4343

theorem not_model4_at286 : Not (AssociativeTheory286 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4343

theorem not_model4_at287 : Not (AssociativeTheory287 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at288 : Not (AssociativeTheory288 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4343

theorem not_model4_at289 : Not (AssociativeTheory289 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at290 : Not (AssociativeTheory290 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at291 : Not (AssociativeTheory291 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at292 : Not (AssociativeTheory292 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at293 : Not (AssociativeTheory293 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4343

theorem not_model4_at294 : Not (AssociativeTheory294 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at295 : Not (AssociativeTheory295 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at296 : Not (AssociativeTheory296 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at297 : Not (AssociativeTheory297 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at298 : Not (AssociativeTheory298 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at299 : Not (AssociativeTheory299 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at300 : Not (AssociativeTheory300 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at301 : Not (AssociativeTheory301 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at302 : Not (AssociativeTheory302 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at303 : Not (AssociativeTheory303 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at304 : Not (AssociativeTheory304 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at305 : Not (AssociativeTheory305 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at306 : Not (AssociativeTheory306 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at307 : Not (AssociativeTheory307 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at308 : Not (AssociativeTheory308 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at309 : Not (AssociativeTheory309 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at310 : Not (AssociativeTheory310 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at311 : Not (AssociativeTheory311 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at312 : Not (AssociativeTheory312 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at313 : Not (AssociativeTheory313 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq308

theorem not_model4_at314 : Not (AssociativeTheory314 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at315 : Not (AssociativeTheory315 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at316 : Not (AssociativeTheory316 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at317 : Not (AssociativeTheory317 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at318 : Not (AssociativeTheory318 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3256

theorem not_model4_at319 : Not (AssociativeTheory319 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at320 : Not (AssociativeTheory320 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at321 : Not (AssociativeTheory321 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at322 : Not (AssociativeTheory322 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at323 : Not (AssociativeTheory323 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at324 : Not (AssociativeTheory324 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at325 : Not (AssociativeTheory325 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at326 : Not (AssociativeTheory326 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at327 : Not (AssociativeTheory327 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at328 : Not (AssociativeTheory328 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at329 : Not (AssociativeTheory329 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at330 : Not (AssociativeTheory330 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at331 : Not (AssociativeTheory331 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at332 : Not (AssociativeTheory332 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at333 : Not (AssociativeTheory333 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at334 : Not (AssociativeTheory334 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at335 : Not (AssociativeTheory335 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at336 : Not (AssociativeTheory336 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at337 : Not (AssociativeTheory337 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at338 : Not (AssociativeTheory338 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at339 : Not (AssociativeTheory339 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at340 : Not (AssociativeTheory340 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4290

theorem not_model4_at341 : Not (AssociativeTheory341 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at342 : Not (AssociativeTheory342 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at343 : Not (AssociativeTheory343 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at344 : Not (AssociativeTheory344 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at345 : Not (AssociativeTheory345 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at346 : Not (AssociativeTheory346 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4343

theorem not_model4_at347 : Not (AssociativeTheory347 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at348 : Not (AssociativeTheory348 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at349 : Not (AssociativeTheory349 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4343

theorem not_model4_at350 : Not (AssociativeTheory350 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at351 : AssociativeTheory351 (Fin 2) :=
  ⟨model4_eq4362, model4_eq4512⟩

theorem model4_at352 : AssociativeTheory352 (Fin 2) :=
  ⟨model4_eq3, model4_eq4362, model4_eq4512⟩

theorem model4_at353 : AssociativeTheory353 (Fin 2) :=
  ⟨model4_eq8, model4_eq4362, model4_eq4512⟩

theorem not_model4_at354 : Not (AssociativeTheory354 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem model4_at355 : AssociativeTheory355 (Fin 2) :=
  ⟨model4_eq47, model4_eq4362, model4_eq4512⟩

theorem model4_at356 : AssociativeTheory356 (Fin 2) :=
  ⟨model4_eq307, model4_eq4362, model4_eq4512⟩

theorem not_model4_at357 : Not (AssociativeTheory357 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem model4_at358 : AssociativeTheory358 (Fin 2) :=
  ⟨model4_eq309, model4_eq4362, model4_eq4512⟩

theorem model4_at359 : AssociativeTheory359 (Fin 2) :=
  ⟨model4_eq323, model4_eq4362, model4_eq4512⟩

theorem model4_at360 : AssociativeTheory360 (Fin 2) :=
  ⟨model4_eq326, model4_eq4362, model4_eq4512⟩

theorem model4_at361 : AssociativeTheory361 (Fin 2) :=
  ⟨model4_eq411, model4_eq4362, model4_eq4512⟩

theorem model4_at362 : AssociativeTheory362 (Fin 2) :=
  ⟨model4_eq3253, model4_eq4362, model4_eq4512⟩

theorem model4_at363 : AssociativeTheory363 (Fin 2) :=
  ⟨model4_eq3261, model4_eq4362, model4_eq4512⟩

theorem not_model4_at364 : Not (AssociativeTheory364 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem model4_at365 : AssociativeTheory365 (Fin 2) :=
  ⟨model4_eq3300, model4_eq4362, model4_eq4512⟩

theorem model4_at366 : AssociativeTheory366 (Fin 2) :=
  ⟨model4_eq3306, model4_eq4362, model4_eq4512⟩

theorem model4_at367 : AssociativeTheory367 (Fin 2) :=
  ⟨model4_eq3319, model4_eq4362, model4_eq4512⟩

theorem not_model4_at368 : Not (AssociativeTheory368 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem model4_at369 : AssociativeTheory369 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4362, model4_eq4512⟩

theorem not_model4_at370 : Not (AssociativeTheory370 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at371 : Not (AssociativeTheory371 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at372 : Not (AssociativeTheory372 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem model4_at373 : AssociativeTheory373 (Fin 2) :=
  ⟨model4_eq4275, model4_eq4362, model4_eq4512⟩

theorem model4_at374 : AssociativeTheory374 (Fin 2) :=
  ⟨model4_eq4269, model4_eq4275, model4_eq4362, model4_eq4512⟩

theorem not_model4_at375 : Not (AssociativeTheory375 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at376 : Not (AssociativeTheory376 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at377 : Not (AssociativeTheory377 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at378 : Not (AssociativeTheory378 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at379 : Not (AssociativeTheory379 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at380 : Not (AssociativeTheory380 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem model4_at381 : AssociativeTheory381 (Fin 2) :=
  ⟨model4_eq4284, model4_eq4362, model4_eq4512⟩

theorem model4_at382 : AssociativeTheory382 (Fin 2) :=
  ⟨model4_eq307, model4_eq4284, model4_eq4362, model4_eq4512⟩

theorem not_model4_at383 : Not (AssociativeTheory383 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at384 : Not (AssociativeTheory384 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at385 : Not (AssociativeTheory385 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at386 : Not (AssociativeTheory386 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at387 : Not (AssociativeTheory387 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at388 : Not (AssociativeTheory388 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at389 : Not (AssociativeTheory389 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at390 : Not (AssociativeTheory390 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at391 : Not (AssociativeTheory391 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4314

theorem not_model4_at392 : Not (AssociativeTheory392 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at393 : Not (AssociativeTheory393 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at394 : Not (AssociativeTheory394 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4293

theorem not_model4_at395 : Not (AssociativeTheory395 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at396 : Not (AssociativeTheory396 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at397 : Not (AssociativeTheory397 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at398 : Not (AssociativeTheory398 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at399 : Not (AssociativeTheory399 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at400 : Not (AssociativeTheory400 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at401 : Not (AssociativeTheory401 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at402 : Not (AssociativeTheory402 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at403 : Not (AssociativeTheory403 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at404 : Not (AssociativeTheory404 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at405 : Not (AssociativeTheory405 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at406 : Not (AssociativeTheory406 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4358

theorem not_model4_at407 : Not (AssociativeTheory407 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at408 : Not (AssociativeTheory408 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4364

theorem not_model4_at409 : Not (AssociativeTheory409 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at410 : Not (AssociativeTheory410 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4364

theorem not_model4_at411 : Not (AssociativeTheory411 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at412 : Not (AssociativeTheory412 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4364

theorem not_model4_at413 : Not (AssociativeTheory413 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at414 : Not (AssociativeTheory414 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at415 : Not (AssociativeTheory415 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at416 : Not (AssociativeTheory416 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at417 : Not (AssociativeTheory417 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4364

theorem not_model4_at418 : Not (AssociativeTheory418 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4364

theorem not_model4_at419 : Not (AssociativeTheory419 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at420 : Not (AssociativeTheory420 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at421 : Not (AssociativeTheory421 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at422 : Not (AssociativeTheory422 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at423 : Not (AssociativeTheory423 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at424 : Not (AssociativeTheory424 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at425 : Not (AssociativeTheory425 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at426 : Not (AssociativeTheory426 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at427 : Not (AssociativeTheory427 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at428 : Not (AssociativeTheory428 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at429 : Not (AssociativeTheory429 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at430 : Not (AssociativeTheory430 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at431 : Not (AssociativeTheory431 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at432 : Not (AssociativeTheory432 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4273

theorem not_model4_at433 : Not (AssociativeTheory433 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at434 : Not (AssociativeTheory434 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4270

theorem not_model4_at435 : Not (AssociativeTheory435 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at436 : Not (AssociativeTheory436 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at437 : Not (AssociativeTheory437 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at438 : Not (AssociativeTheory438 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at439 : Not (AssociativeTheory439 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at440 : Not (AssociativeTheory440 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at441 : Not (AssociativeTheory441 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at442 : Not (AssociativeTheory442 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at443 : Not (AssociativeTheory443 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at444 : Not (AssociativeTheory444 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at445 : Not (AssociativeTheory445 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4283

theorem not_model4_at446 : Not (AssociativeTheory446 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at447 : Not (AssociativeTheory447 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4369

theorem not_model4_at448 : Not (AssociativeTheory448 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at449 : Not (AssociativeTheory449 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at450 : Not (AssociativeTheory450 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq40

theorem not_model4_at451 : Not (AssociativeTheory451 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at452 : Not (AssociativeTheory452 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq3267

theorem not_model4_at453 : Not (AssociativeTheory453 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4268

theorem not_model4_at454 : Not (AssociativeTheory454 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276

theorem not_model4_at455 : Not (AssociativeTheory455 (Fin 2)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4321

theorem not_model4_at456 : Not (AssociativeTheory456 (Fin 2)) := by
  refine not_and_of_not_left _ ?_
  exact not_model4_eq4276
