import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model21_op := finOpTable "[[0,0,0,0,0,0],[0,2,0,4,5,0],[0,0,0,5,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]]"
private def model21 : Magma (Fin 6) where op := model21_op
private instance : Magma (Fin 6) := model21

private theorem model21_eq1 : Equation1 (Fin 6) := by decideFin!
private theorem model21_eq4269 : Equation4269 (Fin 6) := by decideFin!
private theorem model21_eq4270 : Equation4270 (Fin 6) := by decideFin!
private theorem model21_eq4272 : Equation4272 (Fin 6) := by decideFin!
private theorem model21_eq4273 : Equation4273 (Fin 6) := by decideFin!
private theorem model21_eq4276 : Equation4276 (Fin 6) := by decideFin!
private theorem model21_eq4279 : Equation4279 (Fin 6) := by decideFin!
private theorem model21_eq4280 : Equation4280 (Fin 6) := by decideFin!
private theorem model21_eq4314 : Equation4314 (Fin 6) := by decideFin!
private theorem model21_eq4318 : Equation4318 (Fin 6) := by decideFin!
private theorem model21_eq4320 : Equation4320 (Fin 6) := by decideFin!
private theorem model21_eq4321 : Equation4321 (Fin 6) := by decideFin!
private theorem model21_eq4325 : Equation4325 (Fin 6) := by decideFin!
private theorem model21_eq4327 : Equation4327 (Fin 6) := by decideFin!
private theorem model21_eq4331 : Equation4331 (Fin 6) := by decideFin!
private theorem model21_eq4343 : Equation4343 (Fin 6) := by decideFin!
private theorem model21_eq4362 : Equation4362 (Fin 6) := by decideFin!
private theorem model21_eq4512 : Equation4512 (Fin 6) := by decideFin!
private theorem not_model21_eq2 : Not (Equation2 (Fin 6)) := by decideFin!
private theorem not_model21_eq3 : Not (Equation3 (Fin 6)) := by decideFin!
private theorem not_model21_eq4 : Not (Equation4 (Fin 6)) := by decideFin!
private theorem not_model21_eq5 : Not (Equation5 (Fin 6)) := by decideFin!
private theorem not_model21_eq8 : Not (Equation8 (Fin 6)) := by decideFin!
private theorem not_model21_eq10 : Not (Equation10 (Fin 6)) := by decideFin!
private theorem not_model21_eq11 : Not (Equation11 (Fin 6)) := by decideFin!
private theorem not_model21_eq14 : Not (Equation14 (Fin 6)) := by decideFin!
private theorem not_model21_eq16 : Not (Equation16 (Fin 6)) := by decideFin!
private theorem not_model21_eq38 : Not (Equation38 (Fin 6)) := by decideFin!
private theorem not_model21_eq39 : Not (Equation39 (Fin 6)) := by decideFin!
private theorem not_model21_eq40 : Not (Equation40 (Fin 6)) := by decideFin!
private theorem not_model21_eq41 : Not (Equation41 (Fin 6)) := by decideFin!
private theorem not_model21_eq43 : Not (Equation43 (Fin 6)) := by decideFin!
private theorem not_model21_eq47 : Not (Equation47 (Fin 6)) := by decideFin!
private theorem not_model21_eq56 : Not (Equation56 (Fin 6)) := by decideFin!
private theorem not_model21_eq66 : Not (Equation66 (Fin 6)) := by decideFin!
private theorem not_model21_eq75 : Not (Equation75 (Fin 6)) := by decideFin!
private theorem not_model21_eq307 : Not (Equation307 (Fin 6)) := by decideFin!
private theorem not_model21_eq308 : Not (Equation308 (Fin 6)) := by decideFin!
private theorem not_model21_eq309 : Not (Equation309 (Fin 6)) := by decideFin!
private theorem not_model21_eq310 : Not (Equation310 (Fin 6)) := by decideFin!
private theorem not_model21_eq311 : Not (Equation311 (Fin 6)) := by decideFin!
private theorem not_model21_eq312 : Not (Equation312 (Fin 6)) := by decideFin!
private theorem not_model21_eq313 : Not (Equation313 (Fin 6)) := by decideFin!
private theorem not_model21_eq314 : Not (Equation314 (Fin 6)) := by decideFin!
private theorem not_model21_eq315 : Not (Equation315 (Fin 6)) := by decideFin!
private theorem not_model21_eq316 : Not (Equation316 (Fin 6)) := by decideFin!
private theorem not_model21_eq318 : Not (Equation318 (Fin 6)) := by decideFin!
private theorem not_model21_eq323 : Not (Equation323 (Fin 6)) := by decideFin!
private theorem not_model21_eq325 : Not (Equation325 (Fin 6)) := by decideFin!
private theorem not_model21_eq326 : Not (Equation326 (Fin 6)) := by decideFin!
private theorem not_model21_eq327 : Not (Equation327 (Fin 6)) := by decideFin!
private theorem not_model21_eq329 : Not (Equation329 (Fin 6)) := by decideFin!
private theorem not_model21_eq332 : Not (Equation332 (Fin 6)) := by decideFin!
private theorem not_model21_eq333 : Not (Equation333 (Fin 6)) := by decideFin!
private theorem not_model21_eq343 : Not (Equation343 (Fin 6)) := by decideFin!
private theorem not_model21_eq411 : Not (Equation411 (Fin 6)) := by decideFin!
private theorem not_model21_eq419 : Not (Equation419 (Fin 6)) := by decideFin!
private theorem not_model21_eq429 : Not (Equation429 (Fin 6)) := by decideFin!
private theorem not_model21_eq440 : Not (Equation440 (Fin 6)) := by decideFin!
private theorem not_model21_eq477 : Not (Equation477 (Fin 6)) := by decideFin!
private theorem not_model21_eq504 : Not (Equation504 (Fin 6)) := by decideFin!
private theorem not_model21_eq513 : Not (Equation513 (Fin 6)) := by decideFin!
private theorem not_model21_eq3253 : Not (Equation3253 (Fin 6)) := by decideFin!
private theorem not_model21_eq3255 : Not (Equation3255 (Fin 6)) := by decideFin!
private theorem not_model21_eq3256 : Not (Equation3256 (Fin 6)) := by decideFin!
private theorem not_model21_eq3258 : Not (Equation3258 (Fin 6)) := by decideFin!
private theorem not_model21_eq3259 : Not (Equation3259 (Fin 6)) := by decideFin!
private theorem not_model21_eq3260 : Not (Equation3260 (Fin 6)) := by decideFin!
private theorem not_model21_eq3261 : Not (Equation3261 (Fin 6)) := by decideFin!
private theorem not_model21_eq3264 : Not (Equation3264 (Fin 6)) := by decideFin!
private theorem not_model21_eq3265 : Not (Equation3265 (Fin 6)) := by decideFin!
private theorem not_model21_eq3267 : Not (Equation3267 (Fin 6)) := by decideFin!
private theorem not_model21_eq3271 : Not (Equation3271 (Fin 6)) := by decideFin!
private theorem not_model21_eq3273 : Not (Equation3273 (Fin 6)) := by decideFin!
private theorem not_model21_eq3274 : Not (Equation3274 (Fin 6)) := by decideFin!
private theorem not_model21_eq3275 : Not (Equation3275 (Fin 6)) := by decideFin!
private theorem not_model21_eq3277 : Not (Equation3277 (Fin 6)) := by decideFin!
private theorem not_model21_eq3278 : Not (Equation3278 (Fin 6)) := by decideFin!
private theorem not_model21_eq3290 : Not (Equation3290 (Fin 6)) := by decideFin!
private theorem not_model21_eq3292 : Not (Equation3292 (Fin 6)) := by decideFin!
private theorem not_model21_eq3300 : Not (Equation3300 (Fin 6)) := by decideFin!
private theorem not_model21_eq3306 : Not (Equation3306 (Fin 6)) := by decideFin!
private theorem not_model21_eq3308 : Not (Equation3308 (Fin 6)) := by decideFin!
private theorem not_model21_eq3309 : Not (Equation3309 (Fin 6)) := by decideFin!
private theorem not_model21_eq3315 : Not (Equation3315 (Fin 6)) := by decideFin!
private theorem not_model21_eq3316 : Not (Equation3316 (Fin 6)) := by decideFin!
private theorem not_model21_eq3319 : Not (Equation3319 (Fin 6)) := by decideFin!
private theorem not_model21_eq3322 : Not (Equation3322 (Fin 6)) := by decideFin!
private theorem not_model21_eq3323 : Not (Equation3323 (Fin 6)) := by decideFin!
private theorem not_model21_eq3326 : Not (Equation3326 (Fin 6)) := by decideFin!
private theorem not_model21_eq3331 : Not (Equation3331 (Fin 6)) := by decideFin!
private theorem not_model21_eq3334 : Not (Equation3334 (Fin 6)) := by decideFin!
private theorem not_model21_eq3342 : Not (Equation3342 (Fin 6)) := by decideFin!
private theorem not_model21_eq3346 : Not (Equation3346 (Fin 6)) := by decideFin!
private theorem not_model21_eq3350 : Not (Equation3350 (Fin 6)) := by decideFin!
private theorem not_model21_eq3353 : Not (Equation3353 (Fin 6)) := by decideFin!
private theorem not_model21_eq3388 : Not (Equation3388 (Fin 6)) := by decideFin!
private theorem not_model21_eq3414 : Not (Equation3414 (Fin 6)) := by decideFin!
private theorem not_model21_eq4268 : Not (Equation4268 (Fin 6)) := by decideFin!
private theorem not_model21_eq4271 : Not (Equation4271 (Fin 6)) := by decideFin!
private theorem not_model21_eq4274 : Not (Equation4274 (Fin 6)) := by decideFin!
private theorem not_model21_eq4275 : Not (Equation4275 (Fin 6)) := by decideFin!
private theorem not_model21_eq4277 : Not (Equation4277 (Fin 6)) := by decideFin!
private theorem not_model21_eq4278 : Not (Equation4278 (Fin 6)) := by decideFin!
private theorem not_model21_eq4283 : Not (Equation4283 (Fin 6)) := by decideFin!
private theorem not_model21_eq4284 : Not (Equation4284 (Fin 6)) := by decideFin!
private theorem not_model21_eq4286 : Not (Equation4286 (Fin 6)) := by decideFin!
private theorem not_model21_eq4287 : Not (Equation4287 (Fin 6)) := by decideFin!
private theorem not_model21_eq4288 : Not (Equation4288 (Fin 6)) := by decideFin!
private theorem not_model21_eq4290 : Not (Equation4290 (Fin 6)) := by decideFin!
private theorem not_model21_eq4291 : Not (Equation4291 (Fin 6)) := by decideFin!
private theorem not_model21_eq4293 : Not (Equation4293 (Fin 6)) := by decideFin!
private theorem not_model21_eq4296 : Not (Equation4296 (Fin 6)) := by decideFin!
private theorem not_model21_eq4297 : Not (Equation4297 (Fin 6)) := by decideFin!
private theorem not_model21_eq4299 : Not (Equation4299 (Fin 6)) := by decideFin!
private theorem not_model21_eq4300 : Not (Equation4300 (Fin 6)) := by decideFin!
private theorem not_model21_eq4301 : Not (Equation4301 (Fin 6)) := by decideFin!
private theorem not_model21_eq4304 : Not (Equation4304 (Fin 6)) := by decideFin!
private theorem not_model21_eq4305 : Not (Equation4305 (Fin 6)) := by decideFin!
private theorem not_model21_eq4315 : Not (Equation4315 (Fin 6)) := by decideFin!
private theorem not_model21_eq4358 : Not (Equation4358 (Fin 6)) := by decideFin!
private theorem not_model21_eq4364 : Not (Equation4364 (Fin 6)) := by decideFin!
private theorem not_model21_eq4369 : Not (Equation4369 (Fin 6)) := by decideFin!

theorem model21_at1 : AssociativeTheory1 (Fin 6) :=
  model21_eq4512

theorem not_model21_at2 : Not (AssociativeTheory2 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq2

theorem not_model21_at3 : Not (AssociativeTheory3 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3

theorem not_model21_at4 : Not (AssociativeTheory4 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4

theorem not_model21_at5 : Not (AssociativeTheory5 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq5

theorem not_model21_at6 : Not (AssociativeTheory6 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at7 : Not (AssociativeTheory7 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq10

theorem not_model21_at8 : Not (AssociativeTheory8 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq11

theorem not_model21_at9 : Not (AssociativeTheory9 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq14

theorem not_model21_at10 : Not (AssociativeTheory10 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq16

theorem not_model21_at11 : Not (AssociativeTheory11 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq38

theorem not_model21_at12 : Not (AssociativeTheory12 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq39

theorem not_model21_at13 : Not (AssociativeTheory13 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq38

theorem not_model21_at14 : Not (AssociativeTheory14 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at15 : Not (AssociativeTheory15 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at16 : Not (AssociativeTheory16 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3

theorem not_model21_at17 : Not (AssociativeTheory17 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at18 : Not (AssociativeTheory18 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at19 : Not (AssociativeTheory19 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq47

theorem not_model21_at20 : Not (AssociativeTheory20 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at21 : Not (AssociativeTheory21 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq56

theorem not_model21_at22 : Not (AssociativeTheory22 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at23 : Not (AssociativeTheory23 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq75

theorem not_model21_at24 : Not (AssociativeTheory24 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq56

theorem not_model21_at25 : Not (AssociativeTheory25 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at26 : Not (AssociativeTheory26 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at27 : Not (AssociativeTheory27 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at28 : Not (AssociativeTheory28 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at29 : Not (AssociativeTheory29 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq308

theorem not_model21_at30 : Not (AssociativeTheory30 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at31 : Not (AssociativeTheory31 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at32 : Not (AssociativeTheory32 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq308

theorem not_model21_at33 : Not (AssociativeTheory33 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq310

theorem not_model21_at34 : Not (AssociativeTheory34 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq311

theorem not_model21_at35 : Not (AssociativeTheory35 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at36 : Not (AssociativeTheory36 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at37 : Not (AssociativeTheory37 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq312

theorem not_model21_at38 : Not (AssociativeTheory38 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at39 : Not (AssociativeTheory39 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq315

theorem not_model21_at40 : Not (AssociativeTheory40 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq318

theorem not_model21_at41 : Not (AssociativeTheory41 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at42 : Not (AssociativeTheory42 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at43 : Not (AssociativeTheory43 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at44 : Not (AssociativeTheory44 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq312

theorem not_model21_at45 : Not (AssociativeTheory45 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq325

theorem not_model21_at46 : Not (AssociativeTheory46 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3

theorem not_model21_at47 : Not (AssociativeTheory47 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq308

theorem not_model21_at48 : Not (AssociativeTheory48 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at49 : Not (AssociativeTheory49 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at50 : Not (AssociativeTheory50 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at51 : Not (AssociativeTheory51 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq333

theorem not_model21_at52 : Not (AssociativeTheory52 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3

theorem not_model21_at53 : Not (AssociativeTheory53 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at54 : Not (AssociativeTheory54 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq411

theorem not_model21_at55 : Not (AssociativeTheory55 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at56 : Not (AssociativeTheory56 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq419

theorem not_model21_at57 : Not (AssociativeTheory57 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq429

theorem not_model21_at58 : Not (AssociativeTheory58 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq440

theorem not_model21_at59 : Not (AssociativeTheory59 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at60 : Not (AssociativeTheory60 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq504

theorem not_model21_at61 : Not (AssociativeTheory61 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq513

theorem not_model21_at62 : Not (AssociativeTheory62 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq440

theorem not_model21_at63 : Not (AssociativeTheory63 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at64 : Not (AssociativeTheory64 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at65 : Not (AssociativeTheory65 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3255

theorem not_model21_at66 : Not (AssociativeTheory66 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at67 : Not (AssociativeTheory67 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3256

theorem not_model21_at68 : Not (AssociativeTheory68 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3258

theorem not_model21_at69 : Not (AssociativeTheory69 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at70 : Not (AssociativeTheory70 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3255

theorem not_model21_at71 : Not (AssociativeTheory71 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3259

theorem not_model21_at72 : Not (AssociativeTheory72 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3260

theorem not_model21_at73 : Not (AssociativeTheory73 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at74 : Not (AssociativeTheory74 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3261

theorem not_model21_at75 : Not (AssociativeTheory75 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3264

theorem not_model21_at76 : Not (AssociativeTheory76 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at77 : Not (AssociativeTheory77 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq308

theorem not_model21_at78 : Not (AssociativeTheory78 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq312

theorem not_model21_at79 : Not (AssociativeTheory79 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3260

theorem not_model21_at80 : Not (AssociativeTheory80 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at81 : Not (AssociativeTheory81 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3265

theorem not_model21_at82 : Not (AssociativeTheory82 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at83 : Not (AssociativeTheory83 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3260

theorem not_model21_at84 : Not (AssociativeTheory84 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at85 : Not (AssociativeTheory85 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3264

theorem not_model21_at86 : Not (AssociativeTheory86 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at87 : Not (AssociativeTheory87 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3260

theorem not_model21_at88 : Not (AssociativeTheory88 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at89 : Not (AssociativeTheory89 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at90 : Not (AssociativeTheory90 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at91 : Not (AssociativeTheory91 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at92 : Not (AssociativeTheory92 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at93 : Not (AssociativeTheory93 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at94 : Not (AssociativeTheory94 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3271

theorem not_model21_at95 : Not (AssociativeTheory95 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3274

theorem not_model21_at96 : Not (AssociativeTheory96 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3264

theorem not_model21_at97 : Not (AssociativeTheory97 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3278

theorem not_model21_at98 : Not (AssociativeTheory98 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3292

theorem not_model21_at99 : Not (AssociativeTheory99 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3264

theorem not_model21_at100 : Not (AssociativeTheory100 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3274

theorem not_model21_at101 : Not (AssociativeTheory101 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3264

theorem not_model21_at102 : Not (AssociativeTheory102 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3300

theorem not_model21_at103 : Not (AssociativeTheory103 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at104 : Not (AssociativeTheory104 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3306

theorem not_model21_at105 : Not (AssociativeTheory105 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at106 : Not (AssociativeTheory106 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at107 : Not (AssociativeTheory107 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3256

theorem not_model21_at108 : Not (AssociativeTheory108 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3261

theorem not_model21_at109 : Not (AssociativeTheory109 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3271

theorem not_model21_at110 : Not (AssociativeTheory110 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3278

theorem not_model21_at111 : Not (AssociativeTheory111 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3308

theorem not_model21_at112 : Not (AssociativeTheory112 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at113 : Not (AssociativeTheory113 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3315

theorem not_model21_at114 : Not (AssociativeTheory114 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at115 : Not (AssociativeTheory115 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3256

theorem not_model21_at116 : Not (AssociativeTheory116 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3306

theorem not_model21_at117 : Not (AssociativeTheory117 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3316

theorem not_model21_at118 : Not (AssociativeTheory118 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at119 : Not (AssociativeTheory119 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at120 : Not (AssociativeTheory120 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3319

theorem not_model21_at121 : Not (AssociativeTheory121 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3306

theorem not_model21_at122 : Not (AssociativeTheory122 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3346

theorem not_model21_at123 : Not (AssociativeTheory123 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at124 : Not (AssociativeTheory124 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3353

theorem not_model21_at125 : Not (AssociativeTheory125 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at126 : Not (AssociativeTheory126 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3319

theorem not_model21_at127 : Not (AssociativeTheory127 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at128 : Not (AssociativeTheory128 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem model21_at129 : AssociativeTheory129 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4512⟩

theorem not_model21_at130 : Not (AssociativeTheory130 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at131 : AssociativeTheory131 (Fin 6) :=
  ⟨model21_eq4270, model21_eq4512⟩

theorem not_model21_at132 : Not (AssociativeTheory132 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at133 : Not (AssociativeTheory133 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at134 : AssociativeTheory134 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4270, model21_eq4512⟩

theorem not_model21_at135 : Not (AssociativeTheory135 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at136 : Not (AssociativeTheory136 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4271

theorem not_model21_at137 : Not (AssociativeTheory137 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem model21_at138 : AssociativeTheory138 (Fin 6) :=
  ⟨model21_eq4272, model21_eq4512⟩

theorem not_model21_at139 : Not (AssociativeTheory139 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at140 : AssociativeTheory140 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4272, model21_eq4512⟩

theorem not_model21_at141 : Not (AssociativeTheory141 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at142 : AssociativeTheory142 (Fin 6) :=
  ⟨model21_eq4270, model21_eq4272, model21_eq4512⟩

theorem model21_at143 : AssociativeTheory143 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4270, model21_eq4272, model21_eq4512⟩

theorem not_model21_at144 : Not (AssociativeTheory144 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4271

theorem model21_at145 : AssociativeTheory145 (Fin 6) :=
  ⟨model21_eq4273, model21_eq4512⟩

theorem not_model21_at146 : Not (AssociativeTheory146 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at147 : Not (AssociativeTheory147 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at148 : AssociativeTheory148 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4273, model21_eq4512⟩

theorem model21_at149 : AssociativeTheory149 (Fin 6) :=
  ⟨model21_eq4270, model21_eq4273, model21_eq4512⟩

theorem not_model21_at150 : Not (AssociativeTheory150 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at151 : Not (AssociativeTheory151 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at152 : Not (AssociativeTheory152 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at153 : Not (AssociativeTheory153 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at154 : Not (AssociativeTheory154 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at155 : Not (AssociativeTheory155 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at156 : Not (AssociativeTheory156 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at157 : Not (AssociativeTheory157 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem model21_at158 : AssociativeTheory158 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4512⟩

theorem not_model21_at159 : Not (AssociativeTheory159 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at160 : Not (AssociativeTheory160 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4278

theorem not_model21_at161 : Not (AssociativeTheory161 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at162 : Not (AssociativeTheory162 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq47

theorem not_model21_at163 : Not (AssociativeTheory163 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq56

theorem not_model21_at164 : Not (AssociativeTheory164 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at165 : Not (AssociativeTheory165 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at166 : Not (AssociativeTheory166 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq411

theorem not_model21_at167 : Not (AssociativeTheory167 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq440

theorem not_model21_at168 : Not (AssociativeTheory168 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at169 : Not (AssociativeTheory169 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3256

theorem not_model21_at170 : Not (AssociativeTheory170 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3319

theorem not_model21_at171 : Not (AssociativeTheory171 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at172 : Not (AssociativeTheory172 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at173 : Not (AssociativeTheory173 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at174 : Not (AssociativeTheory174 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at175 : Not (AssociativeTheory175 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at176 : Not (AssociativeTheory176 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at177 : Not (AssociativeTheory177 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at178 : Not (AssociativeTheory178 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at179 : Not (AssociativeTheory179 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at180 : Not (AssociativeTheory180 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at181 : Not (AssociativeTheory181 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq43

theorem not_model21_at182 : Not (AssociativeTheory182 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at183 : Not (AssociativeTheory183 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at184 : Not (AssociativeTheory184 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at185 : Not (AssociativeTheory185 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4287

theorem not_model21_at186 : Not (AssociativeTheory186 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at187 : Not (AssociativeTheory187 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at188 : Not (AssociativeTheory188 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at189 : Not (AssociativeTheory189 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq411

theorem not_model21_at190 : Not (AssociativeTheory190 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at191 : Not (AssociativeTheory191 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at192 : Not (AssociativeTheory192 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at193 : Not (AssociativeTheory193 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at194 : Not (AssociativeTheory194 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at195 : Not (AssociativeTheory195 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at196 : Not (AssociativeTheory196 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at197 : Not (AssociativeTheory197 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at198 : Not (AssociativeTheory198 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at199 : Not (AssociativeTheory199 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at200 : Not (AssociativeTheory200 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at201 : Not (AssociativeTheory201 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at202 : Not (AssociativeTheory202 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at203 : Not (AssociativeTheory203 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at204 : Not (AssociativeTheory204 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at205 : Not (AssociativeTheory205 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at206 : Not (AssociativeTheory206 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at207 : Not (AssociativeTheory207 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq312

theorem not_model21_at208 : Not (AssociativeTheory208 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at209 : Not (AssociativeTheory209 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at210 : Not (AssociativeTheory210 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at211 : Not (AssociativeTheory211 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at212 : Not (AssociativeTheory212 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at213 : Not (AssociativeTheory213 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at214 : Not (AssociativeTheory214 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at215 : Not (AssociativeTheory215 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at216 : Not (AssociativeTheory216 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at217 : Not (AssociativeTheory217 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at218 : Not (AssociativeTheory218 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at219 : Not (AssociativeTheory219 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at220 : Not (AssociativeTheory220 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at221 : Not (AssociativeTheory221 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at222 : Not (AssociativeTheory222 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at223 : Not (AssociativeTheory223 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at224 : Not (AssociativeTheory224 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at225 : Not (AssociativeTheory225 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at226 : Not (AssociativeTheory226 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at227 : Not (AssociativeTheory227 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at228 : Not (AssociativeTheory228 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4300

theorem not_model21_at229 : Not (AssociativeTheory229 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem model21_at230 : AssociativeTheory230 (Fin 6) :=
  ⟨model21_eq4314, model21_eq4512⟩

theorem not_model21_at231 : Not (AssociativeTheory231 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at232 : Not (AssociativeTheory232 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq308

theorem not_model21_at233 : Not (AssociativeTheory233 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at234 : Not (AssociativeTheory234 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at235 : Not (AssociativeTheory235 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem model21_at236 : AssociativeTheory236 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4314, model21_eq4512⟩

theorem not_model21_at237 : Not (AssociativeTheory237 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at238 : Not (AssociativeTheory238 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at239 : Not (AssociativeTheory239 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4315

theorem not_model21_at240 : Not (AssociativeTheory240 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem model21_at241 : AssociativeTheory241 (Fin 6) :=
  ⟨model21_eq4320, model21_eq4512⟩

theorem not_model21_at242 : Not (AssociativeTheory242 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq47

theorem not_model21_at243 : Not (AssociativeTheory243 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq75

theorem not_model21_at244 : Not (AssociativeTheory244 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at245 : Not (AssociativeTheory245 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at246 : Not (AssociativeTheory246 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq411

theorem not_model21_at247 : Not (AssociativeTheory247 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq513

theorem not_model21_at248 : Not (AssociativeTheory248 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at249 : Not (AssociativeTheory249 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3261

theorem not_model21_at250 : Not (AssociativeTheory250 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3306

theorem not_model21_at251 : Not (AssociativeTheory251 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at252 : Not (AssociativeTheory252 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem model21_at253 : AssociativeTheory253 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4320, model21_eq4512⟩

theorem not_model21_at254 : Not (AssociativeTheory254 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at255 : Not (AssociativeTheory255 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem model21_at256 : AssociativeTheory256 (Fin 6) :=
  ⟨model21_eq4314, model21_eq4320, model21_eq4512⟩

theorem not_model21_at257 : Not (AssociativeTheory257 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at258 : Not (AssociativeTheory258 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at259 : Not (AssociativeTheory259 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at260 : AssociativeTheory260 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4314, model21_eq4320, model21_eq4512⟩

theorem not_model21_at261 : Not (AssociativeTheory261 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at262 : Not (AssociativeTheory262 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem model21_at263 : AssociativeTheory263 (Fin 6) :=
  ⟨model21_eq4321, model21_eq4512⟩

theorem not_model21_at264 : Not (AssociativeTheory264 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at265 : Not (AssociativeTheory265 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at266 : Not (AssociativeTheory266 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3260

theorem not_model21_at267 : Not (AssociativeTheory267 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3265

theorem not_model21_at268 : Not (AssociativeTheory268 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3260

theorem not_model21_at269 : Not (AssociativeTheory269 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at270 : Not (AssociativeTheory270 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at271 : AssociativeTheory271 (Fin 6) :=
  ⟨model21_eq4270, model21_eq4321, model21_eq4512⟩

theorem not_model21_at272 : Not (AssociativeTheory272 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at273 : AssociativeTheory273 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4321, model21_eq4512⟩

theorem not_model21_at274 : Not (AssociativeTheory274 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at275 : Not (AssociativeTheory275 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at276 : Not (AssociativeTheory276 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at277 : Not (AssociativeTheory277 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at278 : Not (AssociativeTheory278 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at279 : Not (AssociativeTheory279 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at280 : Not (AssociativeTheory280 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at281 : Not (AssociativeTheory281 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at282 : Not (AssociativeTheory282 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at283 : Not (AssociativeTheory283 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at284 : Not (AssociativeTheory284 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem model21_at285 : AssociativeTheory285 (Fin 6) :=
  ⟨model21_eq4343, model21_eq4512⟩

theorem not_model21_at286 : Not (AssociativeTheory286 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at287 : Not (AssociativeTheory287 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at288 : AssociativeTheory288 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4343, model21_eq4512⟩

theorem not_model21_at289 : Not (AssociativeTheory289 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at290 : AssociativeTheory290 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4343, model21_eq4512⟩

theorem not_model21_at291 : Not (AssociativeTheory291 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at292 : Not (AssociativeTheory292 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at293 : Not (AssociativeTheory293 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at294 : Not (AssociativeTheory294 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at295 : Not (AssociativeTheory295 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at296 : Not (AssociativeTheory296 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at297 : Not (AssociativeTheory297 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at298 : Not (AssociativeTheory298 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at299 : Not (AssociativeTheory299 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem model21_at300 : AssociativeTheory300 (Fin 6) :=
  ⟨model21_eq4321, model21_eq4343, model21_eq4512⟩

theorem not_model21_at301 : Not (AssociativeTheory301 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at302 : Not (AssociativeTheory302 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at303 : AssociativeTheory303 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4321, model21_eq4343, model21_eq4512⟩

theorem not_model21_at304 : Not (AssociativeTheory304 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at305 : Not (AssociativeTheory305 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at306 : Not (AssociativeTheory306 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at307 : Not (AssociativeTheory307 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3

theorem not_model21_at308 : Not (AssociativeTheory308 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at309 : Not (AssociativeTheory309 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at310 : Not (AssociativeTheory310 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq47

theorem not_model21_at311 : Not (AssociativeTheory311 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at312 : Not (AssociativeTheory312 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at313 : Not (AssociativeTheory313 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq308

theorem not_model21_at314 : Not (AssociativeTheory314 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at315 : Not (AssociativeTheory315 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at316 : Not (AssociativeTheory316 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq411

theorem not_model21_at317 : Not (AssociativeTheory317 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at318 : Not (AssociativeTheory318 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3256

theorem not_model21_at319 : Not (AssociativeTheory319 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at320 : Not (AssociativeTheory320 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at321 : Not (AssociativeTheory321 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3306

theorem not_model21_at322 : Not (AssociativeTheory322 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3319

theorem not_model21_at323 : Not (AssociativeTheory323 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at324 : Not (AssociativeTheory324 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at325 : Not (AssociativeTheory325 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at326 : Not (AssociativeTheory326 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at327 : Not (AssociativeTheory327 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at328 : Not (AssociativeTheory328 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at329 : Not (AssociativeTheory329 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at330 : Not (AssociativeTheory330 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at331 : Not (AssociativeTheory331 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at332 : Not (AssociativeTheory332 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at333 : Not (AssociativeTheory333 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at334 : Not (AssociativeTheory334 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at335 : Not (AssociativeTheory335 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at336 : Not (AssociativeTheory336 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at337 : Not (AssociativeTheory337 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at338 : Not (AssociativeTheory338 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4290

theorem not_model21_at339 : Not (AssociativeTheory339 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at340 : Not (AssociativeTheory340 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at341 : Not (AssociativeTheory341 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at342 : Not (AssociativeTheory342 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at343 : Not (AssociativeTheory343 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at344 : Not (AssociativeTheory344 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at345 : Not (AssociativeTheory345 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at346 : Not (AssociativeTheory346 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at347 : Not (AssociativeTheory347 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at348 : Not (AssociativeTheory348 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at349 : Not (AssociativeTheory349 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at350 : Not (AssociativeTheory350 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem model21_at351 : AssociativeTheory351 (Fin 6) :=
  ⟨model21_eq4362, model21_eq4512⟩

theorem not_model21_at352 : Not (AssociativeTheory352 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3

theorem not_model21_at353 : Not (AssociativeTheory353 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq8

theorem not_model21_at354 : Not (AssociativeTheory354 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at355 : Not (AssociativeTheory355 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq47

theorem not_model21_at356 : Not (AssociativeTheory356 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at357 : Not (AssociativeTheory357 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at358 : Not (AssociativeTheory358 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at359 : Not (AssociativeTheory359 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq323

theorem not_model21_at360 : Not (AssociativeTheory360 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq326

theorem not_model21_at361 : Not (AssociativeTheory361 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq411

theorem not_model21_at362 : Not (AssociativeTheory362 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at363 : Not (AssociativeTheory363 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3261

theorem not_model21_at364 : Not (AssociativeTheory364 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at365 : Not (AssociativeTheory365 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3300

theorem not_model21_at366 : Not (AssociativeTheory366 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3306

theorem not_model21_at367 : Not (AssociativeTheory367 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3319

theorem not_model21_at368 : Not (AssociativeTheory368 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at369 : AssociativeTheory369 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4362, model21_eq4512⟩

theorem not_model21_at370 : Not (AssociativeTheory370 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at371 : AssociativeTheory371 (Fin 6) :=
  ⟨model21_eq4270, model21_eq4362, model21_eq4512⟩

theorem model21_at372 : AssociativeTheory372 (Fin 6) :=
  ⟨model21_eq4269, model21_eq4270, model21_eq4362, model21_eq4512⟩

theorem not_model21_at373 : Not (AssociativeTheory373 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at374 : Not (AssociativeTheory374 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem not_model21_at375 : Not (AssociativeTheory375 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4275

theorem model21_at376 : AssociativeTheory376 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4362, model21_eq4512⟩

theorem not_model21_at377 : Not (AssociativeTheory377 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at378 : Not (AssociativeTheory378 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at379 : Not (AssociativeTheory379 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at380 : Not (AssociativeTheory380 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at381 : Not (AssociativeTheory381 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at382 : Not (AssociativeTheory382 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at383 : Not (AssociativeTheory383 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at384 : Not (AssociativeTheory384 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at385 : Not (AssociativeTheory385 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at386 : Not (AssociativeTheory386 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at387 : Not (AssociativeTheory387 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at388 : Not (AssociativeTheory388 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at389 : Not (AssociativeTheory389 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem model21_at390 : AssociativeTheory390 (Fin 6) :=
  ⟨model21_eq4314, model21_eq4362, model21_eq4512⟩

theorem not_model21_at391 : Not (AssociativeTheory391 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at392 : Not (AssociativeTheory392 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem model21_at393 : AssociativeTheory393 (Fin 6) :=
  ⟨model21_eq4276, model21_eq4314, model21_eq4362, model21_eq4512⟩

theorem not_model21_at394 : Not (AssociativeTheory394 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at395 : Not (AssociativeTheory395 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4293

theorem not_model21_at396 : Not (AssociativeTheory396 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at397 : Not (AssociativeTheory397 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at398 : Not (AssociativeTheory398 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at399 : Not (AssociativeTheory399 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at400 : Not (AssociativeTheory400 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at401 : Not (AssociativeTheory401 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at402 : Not (AssociativeTheory402 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at403 : Not (AssociativeTheory403 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at404 : Not (AssociativeTheory404 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4358

theorem not_model21_at405 : Not (AssociativeTheory405 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at406 : Not (AssociativeTheory406 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at407 : Not (AssociativeTheory407 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at408 : Not (AssociativeTheory408 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4364

theorem not_model21_at409 : Not (AssociativeTheory409 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at410 : Not (AssociativeTheory410 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at411 : Not (AssociativeTheory411 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at412 : Not (AssociativeTheory412 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at413 : Not (AssociativeTheory413 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at414 : Not (AssociativeTheory414 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at415 : Not (AssociativeTheory415 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4364

theorem not_model21_at416 : Not (AssociativeTheory416 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4364

theorem not_model21_at417 : Not (AssociativeTheory417 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at418 : Not (AssociativeTheory418 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at419 : Not (AssociativeTheory419 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at420 : Not (AssociativeTheory420 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at421 : Not (AssociativeTheory421 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at422 : Not (AssociativeTheory422 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at423 : Not (AssociativeTheory423 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at424 : Not (AssociativeTheory424 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at425 : Not (AssociativeTheory425 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at426 : Not (AssociativeTheory426 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at427 : Not (AssociativeTheory427 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq309

theorem not_model21_at428 : Not (AssociativeTheory428 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at429 : Not (AssociativeTheory429 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at430 : Not (AssociativeTheory430 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at431 : Not (AssociativeTheory431 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at432 : Not (AssociativeTheory432 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at433 : Not (AssociativeTheory433 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at434 : Not (AssociativeTheory434 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at435 : Not (AssociativeTheory435 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at436 : Not (AssociativeTheory436 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at437 : Not (AssociativeTheory437 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at438 : Not (AssociativeTheory438 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3253

theorem not_model21_at439 : Not (AssociativeTheory439 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at440 : Not (AssociativeTheory440 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at441 : Not (AssociativeTheory441 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at442 : Not (AssociativeTheory442 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at443 : Not (AssociativeTheory443 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at444 : Not (AssociativeTheory444 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at445 : Not (AssociativeTheory445 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at446 : Not (AssociativeTheory446 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4283

theorem not_model21_at447 : Not (AssociativeTheory447 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at448 : Not (AssociativeTheory448 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4291

theorem not_model21_at449 : Not (AssociativeTheory449 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at450 : Not (AssociativeTheory450 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq40

theorem not_model21_at451 : Not (AssociativeTheory451 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq307

theorem not_model21_at452 : Not (AssociativeTheory452 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq3267

theorem not_model21_at453 : Not (AssociativeTheory453 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4268

theorem not_model21_at454 : Not (AssociativeTheory454 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4369

theorem not_model21_at455 : Not (AssociativeTheory455 (Fin 6)) := by
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284

theorem not_model21_at456 : Not (AssociativeTheory456 (Fin 6)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model21_eq4284
