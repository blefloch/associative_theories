import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model42_op := finOpTable "[[1,2,2,5,2,6,2,2],[2,2,2,6,2,2,2,2],[2,2,2,2,2,2,2,2],[7,2,2,4,2,2,2,6],[6,2,2,2,2,2,2,2],[2,2,2,2,2,2,2,2],[2,2,2,2,2,2,2,2],[2,2,2,2,2,2,2,2]]"
private def model42 : Magma (Fin 8) where op := model42_op
private instance : Magma (Fin 8) := model42

private theorem model42_eq1 : Equation1 (Fin 8) := by decideFin!
private theorem not_model42_eq2 : Not (Equation2 (Fin 8)) := by decideFin!
private theorem not_model42_eq3 : Not (Equation3 (Fin 8)) := by decideFin!
private theorem not_model42_eq4 : Not (Equation4 (Fin 8)) := by decideFin!
private theorem not_model42_eq5 : Not (Equation5 (Fin 8)) := by decideFin!
private theorem not_model42_eq8 : Not (Equation8 (Fin 8)) := by decideFin!
private theorem not_model42_eq10 : Not (Equation10 (Fin 8)) := by decideFin!
private theorem not_model42_eq11 : Not (Equation11 (Fin 8)) := by decideFin!
private theorem not_model42_eq14 : Not (Equation14 (Fin 8)) := by decideFin!
private theorem not_model42_eq16 : Not (Equation16 (Fin 8)) := by decideFin!
private theorem not_model42_eq38 : Not (Equation38 (Fin 8)) := by decideFin!
private theorem not_model42_eq39 : Not (Equation39 (Fin 8)) := by decideFin!
private theorem not_model42_eq40 : Not (Equation40 (Fin 8)) := by decideFin!
private theorem not_model42_eq41 : Not (Equation41 (Fin 8)) := by decideFin!
private theorem not_model42_eq43 : Not (Equation43 (Fin 8)) := by decideFin!
private theorem not_model42_eq47 : Not (Equation47 (Fin 8)) := by decideFin!
private theorem not_model42_eq56 : Not (Equation56 (Fin 8)) := by decideFin!
private theorem not_model42_eq66 : Not (Equation66 (Fin 8)) := by decideFin!
private theorem not_model42_eq75 : Not (Equation75 (Fin 8)) := by decideFin!
private theorem not_model42_eq307 : Not (Equation307 (Fin 8)) := by decideFin!
private theorem not_model42_eq308 : Not (Equation308 (Fin 8)) := by decideFin!
private theorem not_model42_eq309 : Not (Equation309 (Fin 8)) := by decideFin!
private theorem not_model42_eq310 : Not (Equation310 (Fin 8)) := by decideFin!
private theorem not_model42_eq311 : Not (Equation311 (Fin 8)) := by decideFin!
private theorem not_model42_eq312 : Not (Equation312 (Fin 8)) := by decideFin!
private theorem not_model42_eq313 : Not (Equation313 (Fin 8)) := by decideFin!
private theorem not_model42_eq314 : Not (Equation314 (Fin 8)) := by decideFin!
private theorem not_model42_eq315 : Not (Equation315 (Fin 8)) := by decideFin!
private theorem not_model42_eq316 : Not (Equation316 (Fin 8)) := by decideFin!
private theorem not_model42_eq318 : Not (Equation318 (Fin 8)) := by decideFin!
private theorem not_model42_eq323 : Not (Equation323 (Fin 8)) := by decideFin!
private theorem not_model42_eq325 : Not (Equation325 (Fin 8)) := by decideFin!
private theorem not_model42_eq326 : Not (Equation326 (Fin 8)) := by decideFin!
private theorem not_model42_eq327 : Not (Equation327 (Fin 8)) := by decideFin!
private theorem not_model42_eq329 : Not (Equation329 (Fin 8)) := by decideFin!
private theorem not_model42_eq332 : Not (Equation332 (Fin 8)) := by decideFin!
private theorem not_model42_eq333 : Not (Equation333 (Fin 8)) := by decideFin!
private theorem not_model42_eq343 : Not (Equation343 (Fin 8)) := by decideFin!
private theorem not_model42_eq411 : Not (Equation411 (Fin 8)) := by decideFin!
private theorem not_model42_eq419 : Not (Equation419 (Fin 8)) := by decideFin!
private theorem not_model42_eq429 : Not (Equation429 (Fin 8)) := by decideFin!
private theorem not_model42_eq440 : Not (Equation440 (Fin 8)) := by decideFin!
private theorem not_model42_eq477 : Not (Equation477 (Fin 8)) := by decideFin!
private theorem not_model42_eq504 : Not (Equation504 (Fin 8)) := by decideFin!
private theorem not_model42_eq513 : Not (Equation513 (Fin 8)) := by decideFin!
private theorem not_model42_eq3253 : Not (Equation3253 (Fin 8)) := by decideFin!
private theorem not_model42_eq3255 : Not (Equation3255 (Fin 8)) := by decideFin!
private theorem not_model42_eq3256 : Not (Equation3256 (Fin 8)) := by decideFin!
private theorem not_model42_eq3258 : Not (Equation3258 (Fin 8)) := by decideFin!
private theorem not_model42_eq3259 : Not (Equation3259 (Fin 8)) := by decideFin!
private theorem not_model42_eq3260 : Not (Equation3260 (Fin 8)) := by decideFin!
private theorem not_model42_eq3261 : Not (Equation3261 (Fin 8)) := by decideFin!
private theorem not_model42_eq3264 : Not (Equation3264 (Fin 8)) := by decideFin!
private theorem not_model42_eq3265 : Not (Equation3265 (Fin 8)) := by decideFin!
private theorem not_model42_eq3267 : Not (Equation3267 (Fin 8)) := by decideFin!
private theorem not_model42_eq3271 : Not (Equation3271 (Fin 8)) := by decideFin!
private theorem not_model42_eq3273 : Not (Equation3273 (Fin 8)) := by decideFin!
private theorem not_model42_eq3274 : Not (Equation3274 (Fin 8)) := by decideFin!
private theorem not_model42_eq3275 : Not (Equation3275 (Fin 8)) := by decideFin!
private theorem not_model42_eq3277 : Not (Equation3277 (Fin 8)) := by decideFin!
private theorem not_model42_eq3278 : Not (Equation3278 (Fin 8)) := by decideFin!
private theorem not_model42_eq3290 : Not (Equation3290 (Fin 8)) := by decideFin!
private theorem not_model42_eq3292 : Not (Equation3292 (Fin 8)) := by decideFin!
private theorem not_model42_eq3300 : Not (Equation3300 (Fin 8)) := by decideFin!
private theorem not_model42_eq3306 : Not (Equation3306 (Fin 8)) := by decideFin!
private theorem not_model42_eq3308 : Not (Equation3308 (Fin 8)) := by decideFin!
private theorem not_model42_eq3309 : Not (Equation3309 (Fin 8)) := by decideFin!
private theorem not_model42_eq3315 : Not (Equation3315 (Fin 8)) := by decideFin!
private theorem not_model42_eq3316 : Not (Equation3316 (Fin 8)) := by decideFin!
private theorem not_model42_eq3319 : Not (Equation3319 (Fin 8)) := by decideFin!
private theorem not_model42_eq3322 : Not (Equation3322 (Fin 8)) := by decideFin!
private theorem not_model42_eq3323 : Not (Equation3323 (Fin 8)) := by decideFin!
private theorem not_model42_eq3326 : Not (Equation3326 (Fin 8)) := by decideFin!
private theorem not_model42_eq3331 : Not (Equation3331 (Fin 8)) := by decideFin!
private theorem not_model42_eq3334 : Not (Equation3334 (Fin 8)) := by decideFin!
private theorem not_model42_eq3342 : Not (Equation3342 (Fin 8)) := by decideFin!
private theorem not_model42_eq3346 : Not (Equation3346 (Fin 8)) := by decideFin!
private theorem not_model42_eq3350 : Not (Equation3350 (Fin 8)) := by decideFin!
private theorem not_model42_eq3353 : Not (Equation3353 (Fin 8)) := by decideFin!
private theorem not_model42_eq3388 : Not (Equation3388 (Fin 8)) := by decideFin!
private theorem not_model42_eq3414 : Not (Equation3414 (Fin 8)) := by decideFin!
private theorem not_model42_eq4268 : Not (Equation4268 (Fin 8)) := by decideFin!
private theorem model42_eq4269 : Equation4269 (Fin 8) := by decideFin!
private theorem model42_eq4270 : Equation4270 (Fin 8) := by decideFin!
private theorem not_model42_eq4271 : Not (Equation4271 (Fin 8)) := by decideFin!
private theorem model42_eq4272 : Equation4272 (Fin 8) := by decideFin!
private theorem model42_eq4273 : Equation4273 (Fin 8) := by decideFin!
private theorem not_model42_eq4274 : Not (Equation4274 (Fin 8)) := by decideFin!
private theorem not_model42_eq4275 : Not (Equation4275 (Fin 8)) := by decideFin!
private theorem model42_eq4276 : Equation4276 (Fin 8) := by decideFin!
private theorem not_model42_eq4277 : Not (Equation4277 (Fin 8)) := by decideFin!
private theorem not_model42_eq4278 : Not (Equation4278 (Fin 8)) := by decideFin!
private theorem model42_eq4279 : Equation4279 (Fin 8) := by decideFin!
private theorem model42_eq4280 : Equation4280 (Fin 8) := by decideFin!
private theorem not_model42_eq4283 : Not (Equation4283 (Fin 8)) := by decideFin!
private theorem not_model42_eq4284 : Not (Equation4284 (Fin 8)) := by decideFin!
private theorem not_model42_eq4286 : Not (Equation4286 (Fin 8)) := by decideFin!
private theorem not_model42_eq4287 : Not (Equation4287 (Fin 8)) := by decideFin!
private theorem not_model42_eq4288 : Not (Equation4288 (Fin 8)) := by decideFin!
private theorem not_model42_eq4290 : Not (Equation4290 (Fin 8)) := by decideFin!
private theorem not_model42_eq4291 : Not (Equation4291 (Fin 8)) := by decideFin!
private theorem model42_eq4293 : Equation4293 (Fin 8) := by decideFin!
private theorem not_model42_eq4296 : Not (Equation4296 (Fin 8)) := by decideFin!
private theorem not_model42_eq4297 : Not (Equation4297 (Fin 8)) := by decideFin!
private theorem not_model42_eq4299 : Not (Equation4299 (Fin 8)) := by decideFin!
private theorem not_model42_eq4300 : Not (Equation4300 (Fin 8)) := by decideFin!
private theorem not_model42_eq4301 : Not (Equation4301 (Fin 8)) := by decideFin!
private theorem not_model42_eq4304 : Not (Equation4304 (Fin 8)) := by decideFin!
private theorem not_model42_eq4305 : Not (Equation4305 (Fin 8)) := by decideFin!
private theorem model42_eq4314 : Equation4314 (Fin 8) := by decideFin!
private theorem not_model42_eq4315 : Not (Equation4315 (Fin 8)) := by decideFin!
private theorem model42_eq4318 : Equation4318 (Fin 8) := by decideFin!
private theorem model42_eq4320 : Equation4320 (Fin 8) := by decideFin!
private theorem model42_eq4321 : Equation4321 (Fin 8) := by decideFin!
private theorem model42_eq4325 : Equation4325 (Fin 8) := by decideFin!
private theorem model42_eq4327 : Equation4327 (Fin 8) := by decideFin!
private theorem model42_eq4331 : Equation4331 (Fin 8) := by decideFin!
private theorem model42_eq4343 : Equation4343 (Fin 8) := by decideFin!
private theorem not_model42_eq4358 : Not (Equation4358 (Fin 8)) := by decideFin!
private theorem model42_eq4362 : Equation4362 (Fin 8) := by decideFin!
private theorem not_model42_eq4364 : Not (Equation4364 (Fin 8)) := by decideFin!
private theorem not_model42_eq4369 : Not (Equation4369 (Fin 8)) := by decideFin!
private theorem model42_eq4512 : Equation4512 (Fin 8) := by decideFin!

theorem model42_at1 : AssociativeTheory1 (Fin 8) :=
  model42_eq4512

theorem not_model42_at2 : Not (AssociativeTheory2 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq2

theorem not_model42_at3 : Not (AssociativeTheory3 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3

theorem not_model42_at4 : Not (AssociativeTheory4 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4

theorem not_model42_at5 : Not (AssociativeTheory5 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq5

theorem not_model42_at6 : Not (AssociativeTheory6 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at7 : Not (AssociativeTheory7 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq10

theorem not_model42_at8 : Not (AssociativeTheory8 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq11

theorem not_model42_at9 : Not (AssociativeTheory9 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq14

theorem not_model42_at10 : Not (AssociativeTheory10 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq16

theorem not_model42_at11 : Not (AssociativeTheory11 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq38

theorem not_model42_at12 : Not (AssociativeTheory12 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq39

theorem not_model42_at13 : Not (AssociativeTheory13 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq38

theorem not_model42_at14 : Not (AssociativeTheory14 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at15 : Not (AssociativeTheory15 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at16 : Not (AssociativeTheory16 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3

theorem not_model42_at17 : Not (AssociativeTheory17 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at18 : Not (AssociativeTheory18 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at19 : Not (AssociativeTheory19 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq47

theorem not_model42_at20 : Not (AssociativeTheory20 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at21 : Not (AssociativeTheory21 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq56

theorem not_model42_at22 : Not (AssociativeTheory22 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at23 : Not (AssociativeTheory23 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq75

theorem not_model42_at24 : Not (AssociativeTheory24 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq56

theorem not_model42_at25 : Not (AssociativeTheory25 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at26 : Not (AssociativeTheory26 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at27 : Not (AssociativeTheory27 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at28 : Not (AssociativeTheory28 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at29 : Not (AssociativeTheory29 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq308

theorem not_model42_at30 : Not (AssociativeTheory30 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at31 : Not (AssociativeTheory31 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at32 : Not (AssociativeTheory32 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq308

theorem not_model42_at33 : Not (AssociativeTheory33 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq310

theorem not_model42_at34 : Not (AssociativeTheory34 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq311

theorem not_model42_at35 : Not (AssociativeTheory35 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at36 : Not (AssociativeTheory36 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at37 : Not (AssociativeTheory37 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq312

theorem not_model42_at38 : Not (AssociativeTheory38 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at39 : Not (AssociativeTheory39 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq315

theorem not_model42_at40 : Not (AssociativeTheory40 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq318

theorem not_model42_at41 : Not (AssociativeTheory41 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at42 : Not (AssociativeTheory42 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at43 : Not (AssociativeTheory43 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at44 : Not (AssociativeTheory44 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq312

theorem not_model42_at45 : Not (AssociativeTheory45 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq325

theorem not_model42_at46 : Not (AssociativeTheory46 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3

theorem not_model42_at47 : Not (AssociativeTheory47 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq308

theorem not_model42_at48 : Not (AssociativeTheory48 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at49 : Not (AssociativeTheory49 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at50 : Not (AssociativeTheory50 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at51 : Not (AssociativeTheory51 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq333

theorem not_model42_at52 : Not (AssociativeTheory52 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3

theorem not_model42_at53 : Not (AssociativeTheory53 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at54 : Not (AssociativeTheory54 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq411

theorem not_model42_at55 : Not (AssociativeTheory55 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at56 : Not (AssociativeTheory56 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq419

theorem not_model42_at57 : Not (AssociativeTheory57 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq429

theorem not_model42_at58 : Not (AssociativeTheory58 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq440

theorem not_model42_at59 : Not (AssociativeTheory59 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at60 : Not (AssociativeTheory60 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq504

theorem not_model42_at61 : Not (AssociativeTheory61 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq513

theorem not_model42_at62 : Not (AssociativeTheory62 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq440

theorem not_model42_at63 : Not (AssociativeTheory63 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at64 : Not (AssociativeTheory64 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at65 : Not (AssociativeTheory65 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3255

theorem not_model42_at66 : Not (AssociativeTheory66 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at67 : Not (AssociativeTheory67 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3256

theorem not_model42_at68 : Not (AssociativeTheory68 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3258

theorem not_model42_at69 : Not (AssociativeTheory69 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at70 : Not (AssociativeTheory70 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3255

theorem not_model42_at71 : Not (AssociativeTheory71 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3259

theorem not_model42_at72 : Not (AssociativeTheory72 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3260

theorem not_model42_at73 : Not (AssociativeTheory73 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at74 : Not (AssociativeTheory74 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3261

theorem not_model42_at75 : Not (AssociativeTheory75 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3264

theorem not_model42_at76 : Not (AssociativeTheory76 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at77 : Not (AssociativeTheory77 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq308

theorem not_model42_at78 : Not (AssociativeTheory78 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq312

theorem not_model42_at79 : Not (AssociativeTheory79 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3260

theorem not_model42_at80 : Not (AssociativeTheory80 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at81 : Not (AssociativeTheory81 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3265

theorem not_model42_at82 : Not (AssociativeTheory82 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at83 : Not (AssociativeTheory83 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3260

theorem not_model42_at84 : Not (AssociativeTheory84 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at85 : Not (AssociativeTheory85 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3264

theorem not_model42_at86 : Not (AssociativeTheory86 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at87 : Not (AssociativeTheory87 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3260

theorem not_model42_at88 : Not (AssociativeTheory88 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at89 : Not (AssociativeTheory89 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at90 : Not (AssociativeTheory90 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at91 : Not (AssociativeTheory91 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at92 : Not (AssociativeTheory92 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at93 : Not (AssociativeTheory93 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at94 : Not (AssociativeTheory94 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3271

theorem not_model42_at95 : Not (AssociativeTheory95 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3274

theorem not_model42_at96 : Not (AssociativeTheory96 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3264

theorem not_model42_at97 : Not (AssociativeTheory97 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3278

theorem not_model42_at98 : Not (AssociativeTheory98 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3292

theorem not_model42_at99 : Not (AssociativeTheory99 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3264

theorem not_model42_at100 : Not (AssociativeTheory100 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3274

theorem not_model42_at101 : Not (AssociativeTheory101 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3264

theorem not_model42_at102 : Not (AssociativeTheory102 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3300

theorem not_model42_at103 : Not (AssociativeTheory103 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at104 : Not (AssociativeTheory104 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3306

theorem not_model42_at105 : Not (AssociativeTheory105 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at106 : Not (AssociativeTheory106 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at107 : Not (AssociativeTheory107 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3256

theorem not_model42_at108 : Not (AssociativeTheory108 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3261

theorem not_model42_at109 : Not (AssociativeTheory109 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3271

theorem not_model42_at110 : Not (AssociativeTheory110 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3278

theorem not_model42_at111 : Not (AssociativeTheory111 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3308

theorem not_model42_at112 : Not (AssociativeTheory112 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at113 : Not (AssociativeTheory113 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3315

theorem not_model42_at114 : Not (AssociativeTheory114 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at115 : Not (AssociativeTheory115 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3256

theorem not_model42_at116 : Not (AssociativeTheory116 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3306

theorem not_model42_at117 : Not (AssociativeTheory117 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3316

theorem not_model42_at118 : Not (AssociativeTheory118 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at119 : Not (AssociativeTheory119 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at120 : Not (AssociativeTheory120 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3319

theorem not_model42_at121 : Not (AssociativeTheory121 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3306

theorem not_model42_at122 : Not (AssociativeTheory122 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3346

theorem not_model42_at123 : Not (AssociativeTheory123 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at124 : Not (AssociativeTheory124 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3353

theorem not_model42_at125 : Not (AssociativeTheory125 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at126 : Not (AssociativeTheory126 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3319

theorem not_model42_at127 : Not (AssociativeTheory127 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at128 : Not (AssociativeTheory128 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem model42_at129 : AssociativeTheory129 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4512⟩

theorem not_model42_at130 : Not (AssociativeTheory130 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at131 : AssociativeTheory131 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4512⟩

theorem not_model42_at132 : Not (AssociativeTheory132 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at133 : Not (AssociativeTheory133 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at134 : AssociativeTheory134 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4270, model42_eq4512⟩

theorem not_model42_at135 : Not (AssociativeTheory135 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at136 : Not (AssociativeTheory136 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4271

theorem not_model42_at137 : Not (AssociativeTheory137 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem model42_at138 : AssociativeTheory138 (Fin 8) :=
  ⟨model42_eq4272, model42_eq4512⟩

theorem not_model42_at139 : Not (AssociativeTheory139 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at140 : AssociativeTheory140 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4272, model42_eq4512⟩

theorem not_model42_at141 : Not (AssociativeTheory141 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at142 : AssociativeTheory142 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4272, model42_eq4512⟩

theorem model42_at143 : AssociativeTheory143 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4270, model42_eq4272, model42_eq4512⟩

theorem not_model42_at144 : Not (AssociativeTheory144 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4271

theorem model42_at145 : AssociativeTheory145 (Fin 8) :=
  ⟨model42_eq4273, model42_eq4512⟩

theorem not_model42_at146 : Not (AssociativeTheory146 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at147 : Not (AssociativeTheory147 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at148 : AssociativeTheory148 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4273, model42_eq4512⟩

theorem model42_at149 : AssociativeTheory149 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4273, model42_eq4512⟩

theorem not_model42_at150 : Not (AssociativeTheory150 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at151 : Not (AssociativeTheory151 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at152 : Not (AssociativeTheory152 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at153 : Not (AssociativeTheory153 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at154 : Not (AssociativeTheory154 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at155 : Not (AssociativeTheory155 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at156 : Not (AssociativeTheory156 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at157 : Not (AssociativeTheory157 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem model42_at158 : AssociativeTheory158 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4512⟩

theorem not_model42_at159 : Not (AssociativeTheory159 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at160 : Not (AssociativeTheory160 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4278

theorem not_model42_at161 : Not (AssociativeTheory161 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at162 : Not (AssociativeTheory162 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq47

theorem not_model42_at163 : Not (AssociativeTheory163 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq56

theorem not_model42_at164 : Not (AssociativeTheory164 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at165 : Not (AssociativeTheory165 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at166 : Not (AssociativeTheory166 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq411

theorem not_model42_at167 : Not (AssociativeTheory167 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq440

theorem not_model42_at168 : Not (AssociativeTheory168 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at169 : Not (AssociativeTheory169 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3256

theorem not_model42_at170 : Not (AssociativeTheory170 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3319

theorem not_model42_at171 : Not (AssociativeTheory171 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at172 : Not (AssociativeTheory172 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at173 : Not (AssociativeTheory173 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at174 : Not (AssociativeTheory174 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at175 : Not (AssociativeTheory175 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at176 : Not (AssociativeTheory176 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at177 : Not (AssociativeTheory177 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at178 : Not (AssociativeTheory178 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at179 : Not (AssociativeTheory179 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at180 : Not (AssociativeTheory180 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at181 : Not (AssociativeTheory181 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq43

theorem not_model42_at182 : Not (AssociativeTheory182 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at183 : Not (AssociativeTheory183 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at184 : Not (AssociativeTheory184 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at185 : Not (AssociativeTheory185 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4287

theorem not_model42_at186 : Not (AssociativeTheory186 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at187 : Not (AssociativeTheory187 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at188 : Not (AssociativeTheory188 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at189 : Not (AssociativeTheory189 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq411

theorem not_model42_at190 : Not (AssociativeTheory190 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at191 : Not (AssociativeTheory191 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at192 : Not (AssociativeTheory192 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at193 : Not (AssociativeTheory193 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at194 : Not (AssociativeTheory194 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at195 : Not (AssociativeTheory195 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at196 : Not (AssociativeTheory196 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at197 : Not (AssociativeTheory197 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at198 : Not (AssociativeTheory198 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at199 : Not (AssociativeTheory199 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at200 : Not (AssociativeTheory200 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at201 : Not (AssociativeTheory201 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at202 : Not (AssociativeTheory202 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at203 : Not (AssociativeTheory203 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at204 : Not (AssociativeTheory204 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at205 : Not (AssociativeTheory205 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at206 : Not (AssociativeTheory206 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at207 : Not (AssociativeTheory207 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq312

theorem not_model42_at208 : Not (AssociativeTheory208 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at209 : Not (AssociativeTheory209 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at210 : Not (AssociativeTheory210 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at211 : Not (AssociativeTheory211 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at212 : Not (AssociativeTheory212 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at213 : Not (AssociativeTheory213 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at214 : Not (AssociativeTheory214 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at215 : Not (AssociativeTheory215 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at216 : Not (AssociativeTheory216 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at217 : Not (AssociativeTheory217 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at218 : Not (AssociativeTheory218 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at219 : Not (AssociativeTheory219 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at220 : Not (AssociativeTheory220 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at221 : Not (AssociativeTheory221 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem model42_at222 : AssociativeTheory222 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4512⟩

theorem not_model42_at223 : Not (AssociativeTheory223 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem model42_at224 : AssociativeTheory224 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4293, model42_eq4512⟩

theorem model42_at225 : AssociativeTheory225 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4293, model42_eq4512⟩

theorem model42_at226 : AssociativeTheory226 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4270, model42_eq4293, model42_eq4512⟩

theorem model42_at227 : AssociativeTheory227 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4512⟩

theorem not_model42_at228 : Not (AssociativeTheory228 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4300

theorem not_model42_at229 : Not (AssociativeTheory229 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem model42_at230 : AssociativeTheory230 (Fin 8) :=
  ⟨model42_eq4314, model42_eq4512⟩

theorem not_model42_at231 : Not (AssociativeTheory231 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at232 : Not (AssociativeTheory232 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq308

theorem not_model42_at233 : Not (AssociativeTheory233 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at234 : Not (AssociativeTheory234 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at235 : Not (AssociativeTheory235 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem model42_at236 : AssociativeTheory236 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4314, model42_eq4512⟩

theorem model42_at237 : AssociativeTheory237 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4314, model42_eq4512⟩

theorem model42_at238 : AssociativeTheory238 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4314, model42_eq4512⟩

theorem not_model42_at239 : Not (AssociativeTheory239 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4315

theorem not_model42_at240 : Not (AssociativeTheory240 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem model42_at241 : AssociativeTheory241 (Fin 8) :=
  ⟨model42_eq4320, model42_eq4512⟩

theorem not_model42_at242 : Not (AssociativeTheory242 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq47

theorem not_model42_at243 : Not (AssociativeTheory243 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq75

theorem not_model42_at244 : Not (AssociativeTheory244 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at245 : Not (AssociativeTheory245 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at246 : Not (AssociativeTheory246 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq411

theorem not_model42_at247 : Not (AssociativeTheory247 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq513

theorem not_model42_at248 : Not (AssociativeTheory248 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at249 : Not (AssociativeTheory249 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3261

theorem not_model42_at250 : Not (AssociativeTheory250 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3306

theorem not_model42_at251 : Not (AssociativeTheory251 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at252 : Not (AssociativeTheory252 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem model42_at253 : AssociativeTheory253 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4320, model42_eq4512⟩

theorem model42_at254 : AssociativeTheory254 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4320, model42_eq4512⟩

theorem model42_at255 : AssociativeTheory255 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4320, model42_eq4512⟩

theorem model42_at256 : AssociativeTheory256 (Fin 8) :=
  ⟨model42_eq4314, model42_eq4320, model42_eq4512⟩

theorem not_model42_at257 : Not (AssociativeTheory257 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at258 : Not (AssociativeTheory258 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at259 : Not (AssociativeTheory259 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at260 : AssociativeTheory260 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4314, model42_eq4320, model42_eq4512⟩

theorem model42_at261 : AssociativeTheory261 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4314, model42_eq4320, model42_eq4512⟩

theorem model42_at262 : AssociativeTheory262 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4314, model42_eq4320, model42_eq4512⟩

theorem model42_at263 : AssociativeTheory263 (Fin 8) :=
  ⟨model42_eq4321, model42_eq4512⟩

theorem not_model42_at264 : Not (AssociativeTheory264 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at265 : Not (AssociativeTheory265 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at266 : Not (AssociativeTheory266 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3260

theorem not_model42_at267 : Not (AssociativeTheory267 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3265

theorem not_model42_at268 : Not (AssociativeTheory268 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3260

theorem not_model42_at269 : Not (AssociativeTheory269 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at270 : Not (AssociativeTheory270 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at271 : AssociativeTheory271 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4321, model42_eq4512⟩

theorem not_model42_at272 : Not (AssociativeTheory272 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at273 : AssociativeTheory273 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4321, model42_eq4512⟩

theorem not_model42_at274 : Not (AssociativeTheory274 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at275 : Not (AssociativeTheory275 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at276 : Not (AssociativeTheory276 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at277 : Not (AssociativeTheory277 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at278 : Not (AssociativeTheory278 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at279 : Not (AssociativeTheory279 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at280 : Not (AssociativeTheory280 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem model42_at281 : AssociativeTheory281 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4321, model42_eq4512⟩

theorem not_model42_at282 : Not (AssociativeTheory282 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem model42_at283 : AssociativeTheory283 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4293, model42_eq4321, model42_eq4512⟩

theorem model42_at284 : AssociativeTheory284 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4321, model42_eq4512⟩

theorem model42_at285 : AssociativeTheory285 (Fin 8) :=
  ⟨model42_eq4343, model42_eq4512⟩

theorem not_model42_at286 : Not (AssociativeTheory286 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at287 : Not (AssociativeTheory287 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at288 : AssociativeTheory288 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4343, model42_eq4512⟩

theorem not_model42_at289 : Not (AssociativeTheory289 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at290 : AssociativeTheory290 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4343, model42_eq4512⟩

theorem not_model42_at291 : Not (AssociativeTheory291 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at292 : Not (AssociativeTheory292 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at293 : Not (AssociativeTheory293 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at294 : Not (AssociativeTheory294 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at295 : Not (AssociativeTheory295 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at296 : Not (AssociativeTheory296 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem model42_at297 : AssociativeTheory297 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4343, model42_eq4512⟩

theorem model42_at298 : AssociativeTheory298 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4293, model42_eq4343, model42_eq4512⟩

theorem model42_at299 : AssociativeTheory299 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4343, model42_eq4512⟩

theorem model42_at300 : AssociativeTheory300 (Fin 8) :=
  ⟨model42_eq4321, model42_eq4343, model42_eq4512⟩

theorem not_model42_at301 : Not (AssociativeTheory301 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at302 : Not (AssociativeTheory302 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at303 : AssociativeTheory303 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4321, model42_eq4343, model42_eq4512⟩

theorem model42_at304 : AssociativeTheory304 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4321, model42_eq4343, model42_eq4512⟩

theorem model42_at305 : AssociativeTheory305 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4321, model42_eq4343, model42_eq4512⟩

theorem not_model42_at306 : Not (AssociativeTheory306 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at307 : Not (AssociativeTheory307 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3

theorem not_model42_at308 : Not (AssociativeTheory308 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at309 : Not (AssociativeTheory309 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at310 : Not (AssociativeTheory310 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq47

theorem not_model42_at311 : Not (AssociativeTheory311 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at312 : Not (AssociativeTheory312 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at313 : Not (AssociativeTheory313 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq308

theorem not_model42_at314 : Not (AssociativeTheory314 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at315 : Not (AssociativeTheory315 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at316 : Not (AssociativeTheory316 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq411

theorem not_model42_at317 : Not (AssociativeTheory317 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at318 : Not (AssociativeTheory318 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3256

theorem not_model42_at319 : Not (AssociativeTheory319 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at320 : Not (AssociativeTheory320 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at321 : Not (AssociativeTheory321 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3306

theorem not_model42_at322 : Not (AssociativeTheory322 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3319

theorem not_model42_at323 : Not (AssociativeTheory323 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at324 : Not (AssociativeTheory324 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at325 : Not (AssociativeTheory325 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at326 : Not (AssociativeTheory326 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at327 : Not (AssociativeTheory327 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at328 : Not (AssociativeTheory328 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at329 : Not (AssociativeTheory329 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at330 : Not (AssociativeTheory330 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at331 : Not (AssociativeTheory331 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at332 : Not (AssociativeTheory332 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at333 : Not (AssociativeTheory333 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at334 : Not (AssociativeTheory334 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at335 : Not (AssociativeTheory335 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at336 : Not (AssociativeTheory336 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at337 : Not (AssociativeTheory337 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at338 : Not (AssociativeTheory338 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4290

theorem not_model42_at339 : Not (AssociativeTheory339 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at340 : Not (AssociativeTheory340 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at341 : Not (AssociativeTheory341 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at342 : Not (AssociativeTheory342 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at343 : Not (AssociativeTheory343 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at344 : Not (AssociativeTheory344 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at345 : Not (AssociativeTheory345 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at346 : Not (AssociativeTheory346 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at347 : Not (AssociativeTheory347 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at348 : Not (AssociativeTheory348 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at349 : Not (AssociativeTheory349 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at350 : Not (AssociativeTheory350 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem model42_at351 : AssociativeTheory351 (Fin 8) :=
  ⟨model42_eq4362, model42_eq4512⟩

theorem not_model42_at352 : Not (AssociativeTheory352 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3

theorem not_model42_at353 : Not (AssociativeTheory353 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq8

theorem not_model42_at354 : Not (AssociativeTheory354 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at355 : Not (AssociativeTheory355 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq47

theorem not_model42_at356 : Not (AssociativeTheory356 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at357 : Not (AssociativeTheory357 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at358 : Not (AssociativeTheory358 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at359 : Not (AssociativeTheory359 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq323

theorem not_model42_at360 : Not (AssociativeTheory360 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq326

theorem not_model42_at361 : Not (AssociativeTheory361 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq411

theorem not_model42_at362 : Not (AssociativeTheory362 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at363 : Not (AssociativeTheory363 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3261

theorem not_model42_at364 : Not (AssociativeTheory364 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at365 : Not (AssociativeTheory365 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3300

theorem not_model42_at366 : Not (AssociativeTheory366 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3306

theorem not_model42_at367 : Not (AssociativeTheory367 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3319

theorem not_model42_at368 : Not (AssociativeTheory368 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at369 : AssociativeTheory369 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4362, model42_eq4512⟩

theorem not_model42_at370 : Not (AssociativeTheory370 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at371 : AssociativeTheory371 (Fin 8) :=
  ⟨model42_eq4270, model42_eq4362, model42_eq4512⟩

theorem model42_at372 : AssociativeTheory372 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4270, model42_eq4362, model42_eq4512⟩

theorem not_model42_at373 : Not (AssociativeTheory373 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at374 : Not (AssociativeTheory374 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem not_model42_at375 : Not (AssociativeTheory375 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4275

theorem model42_at376 : AssociativeTheory376 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4362, model42_eq4512⟩

theorem not_model42_at377 : Not (AssociativeTheory377 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at378 : Not (AssociativeTheory378 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at379 : Not (AssociativeTheory379 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at380 : Not (AssociativeTheory380 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at381 : Not (AssociativeTheory381 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at382 : Not (AssociativeTheory382 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at383 : Not (AssociativeTheory383 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at384 : Not (AssociativeTheory384 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at385 : Not (AssociativeTheory385 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at386 : Not (AssociativeTheory386 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem model42_at387 : AssociativeTheory387 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4362, model42_eq4512⟩

theorem model42_at388 : AssociativeTheory388 (Fin 8) :=
  ⟨model42_eq4269, model42_eq4293, model42_eq4362, model42_eq4512⟩

theorem model42_at389 : AssociativeTheory389 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4362, model42_eq4512⟩

theorem model42_at390 : AssociativeTheory390 (Fin 8) :=
  ⟨model42_eq4314, model42_eq4362, model42_eq4512⟩

theorem not_model42_at391 : Not (AssociativeTheory391 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at392 : Not (AssociativeTheory392 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem model42_at393 : AssociativeTheory393 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4314, model42_eq4362, model42_eq4512⟩

theorem model42_at394 : AssociativeTheory394 (Fin 8) :=
  ⟨model42_eq4293, model42_eq4314, model42_eq4362, model42_eq4512⟩

theorem model42_at395 : AssociativeTheory395 (Fin 8) :=
  ⟨model42_eq4276, model42_eq4293, model42_eq4314, model42_eq4362, model42_eq4512⟩

theorem not_model42_at396 : Not (AssociativeTheory396 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at397 : Not (AssociativeTheory397 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at398 : Not (AssociativeTheory398 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at399 : Not (AssociativeTheory399 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at400 : Not (AssociativeTheory400 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at401 : Not (AssociativeTheory401 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at402 : Not (AssociativeTheory402 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at403 : Not (AssociativeTheory403 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at404 : Not (AssociativeTheory404 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4358

theorem not_model42_at405 : Not (AssociativeTheory405 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at406 : Not (AssociativeTheory406 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at407 : Not (AssociativeTheory407 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at408 : Not (AssociativeTheory408 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4364

theorem not_model42_at409 : Not (AssociativeTheory409 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at410 : Not (AssociativeTheory410 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at411 : Not (AssociativeTheory411 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at412 : Not (AssociativeTheory412 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at413 : Not (AssociativeTheory413 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at414 : Not (AssociativeTheory414 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at415 : Not (AssociativeTheory415 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4364

theorem not_model42_at416 : Not (AssociativeTheory416 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4364

theorem not_model42_at417 : Not (AssociativeTheory417 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at418 : Not (AssociativeTheory418 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at419 : Not (AssociativeTheory419 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at420 : Not (AssociativeTheory420 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at421 : Not (AssociativeTheory421 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at422 : Not (AssociativeTheory422 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at423 : Not (AssociativeTheory423 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at424 : Not (AssociativeTheory424 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at425 : Not (AssociativeTheory425 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at426 : Not (AssociativeTheory426 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at427 : Not (AssociativeTheory427 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq309

theorem not_model42_at428 : Not (AssociativeTheory428 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at429 : Not (AssociativeTheory429 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at430 : Not (AssociativeTheory430 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at431 : Not (AssociativeTheory431 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at432 : Not (AssociativeTheory432 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at433 : Not (AssociativeTheory433 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at434 : Not (AssociativeTheory434 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at435 : Not (AssociativeTheory435 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at436 : Not (AssociativeTheory436 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at437 : Not (AssociativeTheory437 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at438 : Not (AssociativeTheory438 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3253

theorem not_model42_at439 : Not (AssociativeTheory439 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at440 : Not (AssociativeTheory440 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at441 : Not (AssociativeTheory441 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at442 : Not (AssociativeTheory442 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at443 : Not (AssociativeTheory443 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at444 : Not (AssociativeTheory444 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at445 : Not (AssociativeTheory445 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at446 : Not (AssociativeTheory446 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4283

theorem not_model42_at447 : Not (AssociativeTheory447 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at448 : Not (AssociativeTheory448 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4291

theorem not_model42_at449 : Not (AssociativeTheory449 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at450 : Not (AssociativeTheory450 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq40

theorem not_model42_at451 : Not (AssociativeTheory451 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq307

theorem not_model42_at452 : Not (AssociativeTheory452 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq3267

theorem not_model42_at453 : Not (AssociativeTheory453 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4268

theorem not_model42_at454 : Not (AssociativeTheory454 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4369

theorem not_model42_at455 : Not (AssociativeTheory455 (Fin 8)) := by
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284

theorem not_model42_at456 : Not (AssociativeTheory456 (Fin 8)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model42_eq4284
