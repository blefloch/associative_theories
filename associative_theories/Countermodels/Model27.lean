import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model27_op := finOpTable "[[1,2,2,6,2,4,2],[2,2,2,2,2,2,2],[2,2,2,2,2,2,2],[5,4,2,2,2,2,2],[2,2,2,2,2,2,2],[4,2,2,2,2,2,2],[4,2,2,2,2,2,2]]"
private def model27 : Magma (Fin 7) where op := model27_op
private instance : Magma (Fin 7) := model27

private theorem model27_eq1 : Equation1 (Fin 7) := by decideFin!
private theorem model27_eq4268 : Equation4268 (Fin 7) := by decideFin!
private theorem model27_eq4275 : Equation4275 (Fin 7) := by decideFin!
private theorem model27_eq4276 : Equation4276 (Fin 7) := by decideFin!
private theorem model27_eq4277 : Equation4277 (Fin 7) := by decideFin!
private theorem model27_eq4293 : Equation4293 (Fin 7) := by decideFin!
private theorem model27_eq4320 : Equation4320 (Fin 7) := by decideFin!
private theorem model27_eq4362 : Equation4362 (Fin 7) := by decideFin!
private theorem model27_eq4512 : Equation4512 (Fin 7) := by decideFin!
private theorem not_model27_eq2 : Not (Equation2 (Fin 7)) := by decideFin!
private theorem not_model27_eq3 : Not (Equation3 (Fin 7)) := by decideFin!
private theorem not_model27_eq4 : Not (Equation4 (Fin 7)) := by decideFin!
private theorem not_model27_eq5 : Not (Equation5 (Fin 7)) := by decideFin!
private theorem not_model27_eq8 : Not (Equation8 (Fin 7)) := by decideFin!
private theorem not_model27_eq10 : Not (Equation10 (Fin 7)) := by decideFin!
private theorem not_model27_eq11 : Not (Equation11 (Fin 7)) := by decideFin!
private theorem not_model27_eq14 : Not (Equation14 (Fin 7)) := by decideFin!
private theorem not_model27_eq16 : Not (Equation16 (Fin 7)) := by decideFin!
private theorem not_model27_eq38 : Not (Equation38 (Fin 7)) := by decideFin!
private theorem not_model27_eq39 : Not (Equation39 (Fin 7)) := by decideFin!
private theorem not_model27_eq40 : Not (Equation40 (Fin 7)) := by decideFin!
private theorem not_model27_eq41 : Not (Equation41 (Fin 7)) := by decideFin!
private theorem not_model27_eq43 : Not (Equation43 (Fin 7)) := by decideFin!
private theorem not_model27_eq47 : Not (Equation47 (Fin 7)) := by decideFin!
private theorem not_model27_eq56 : Not (Equation56 (Fin 7)) := by decideFin!
private theorem not_model27_eq66 : Not (Equation66 (Fin 7)) := by decideFin!
private theorem not_model27_eq75 : Not (Equation75 (Fin 7)) := by decideFin!
private theorem not_model27_eq307 : Not (Equation307 (Fin 7)) := by decideFin!
private theorem not_model27_eq308 : Not (Equation308 (Fin 7)) := by decideFin!
private theorem not_model27_eq309 : Not (Equation309 (Fin 7)) := by decideFin!
private theorem not_model27_eq310 : Not (Equation310 (Fin 7)) := by decideFin!
private theorem not_model27_eq311 : Not (Equation311 (Fin 7)) := by decideFin!
private theorem not_model27_eq312 : Not (Equation312 (Fin 7)) := by decideFin!
private theorem not_model27_eq313 : Not (Equation313 (Fin 7)) := by decideFin!
private theorem not_model27_eq314 : Not (Equation314 (Fin 7)) := by decideFin!
private theorem not_model27_eq315 : Not (Equation315 (Fin 7)) := by decideFin!
private theorem not_model27_eq316 : Not (Equation316 (Fin 7)) := by decideFin!
private theorem not_model27_eq318 : Not (Equation318 (Fin 7)) := by decideFin!
private theorem not_model27_eq323 : Not (Equation323 (Fin 7)) := by decideFin!
private theorem not_model27_eq325 : Not (Equation325 (Fin 7)) := by decideFin!
private theorem not_model27_eq326 : Not (Equation326 (Fin 7)) := by decideFin!
private theorem not_model27_eq327 : Not (Equation327 (Fin 7)) := by decideFin!
private theorem not_model27_eq329 : Not (Equation329 (Fin 7)) := by decideFin!
private theorem not_model27_eq332 : Not (Equation332 (Fin 7)) := by decideFin!
private theorem not_model27_eq333 : Not (Equation333 (Fin 7)) := by decideFin!
private theorem not_model27_eq343 : Not (Equation343 (Fin 7)) := by decideFin!
private theorem not_model27_eq411 : Not (Equation411 (Fin 7)) := by decideFin!
private theorem not_model27_eq419 : Not (Equation419 (Fin 7)) := by decideFin!
private theorem not_model27_eq429 : Not (Equation429 (Fin 7)) := by decideFin!
private theorem not_model27_eq440 : Not (Equation440 (Fin 7)) := by decideFin!
private theorem not_model27_eq477 : Not (Equation477 (Fin 7)) := by decideFin!
private theorem not_model27_eq504 : Not (Equation504 (Fin 7)) := by decideFin!
private theorem not_model27_eq513 : Not (Equation513 (Fin 7)) := by decideFin!
private theorem not_model27_eq3253 : Not (Equation3253 (Fin 7)) := by decideFin!
private theorem not_model27_eq3255 : Not (Equation3255 (Fin 7)) := by decideFin!
private theorem not_model27_eq3256 : Not (Equation3256 (Fin 7)) := by decideFin!
private theorem not_model27_eq3258 : Not (Equation3258 (Fin 7)) := by decideFin!
private theorem not_model27_eq3259 : Not (Equation3259 (Fin 7)) := by decideFin!
private theorem not_model27_eq3260 : Not (Equation3260 (Fin 7)) := by decideFin!
private theorem not_model27_eq3261 : Not (Equation3261 (Fin 7)) := by decideFin!
private theorem not_model27_eq3264 : Not (Equation3264 (Fin 7)) := by decideFin!
private theorem not_model27_eq3265 : Not (Equation3265 (Fin 7)) := by decideFin!
private theorem not_model27_eq3267 : Not (Equation3267 (Fin 7)) := by decideFin!
private theorem not_model27_eq3271 : Not (Equation3271 (Fin 7)) := by decideFin!
private theorem not_model27_eq3273 : Not (Equation3273 (Fin 7)) := by decideFin!
private theorem not_model27_eq3274 : Not (Equation3274 (Fin 7)) := by decideFin!
private theorem not_model27_eq3275 : Not (Equation3275 (Fin 7)) := by decideFin!
private theorem not_model27_eq3277 : Not (Equation3277 (Fin 7)) := by decideFin!
private theorem not_model27_eq3278 : Not (Equation3278 (Fin 7)) := by decideFin!
private theorem not_model27_eq3290 : Not (Equation3290 (Fin 7)) := by decideFin!
private theorem not_model27_eq3292 : Not (Equation3292 (Fin 7)) := by decideFin!
private theorem not_model27_eq3300 : Not (Equation3300 (Fin 7)) := by decideFin!
private theorem not_model27_eq3306 : Not (Equation3306 (Fin 7)) := by decideFin!
private theorem not_model27_eq3308 : Not (Equation3308 (Fin 7)) := by decideFin!
private theorem not_model27_eq3309 : Not (Equation3309 (Fin 7)) := by decideFin!
private theorem not_model27_eq3315 : Not (Equation3315 (Fin 7)) := by decideFin!
private theorem not_model27_eq3316 : Not (Equation3316 (Fin 7)) := by decideFin!
private theorem not_model27_eq3319 : Not (Equation3319 (Fin 7)) := by decideFin!
private theorem not_model27_eq3322 : Not (Equation3322 (Fin 7)) := by decideFin!
private theorem not_model27_eq3323 : Not (Equation3323 (Fin 7)) := by decideFin!
private theorem not_model27_eq3326 : Not (Equation3326 (Fin 7)) := by decideFin!
private theorem not_model27_eq3331 : Not (Equation3331 (Fin 7)) := by decideFin!
private theorem not_model27_eq3334 : Not (Equation3334 (Fin 7)) := by decideFin!
private theorem not_model27_eq3342 : Not (Equation3342 (Fin 7)) := by decideFin!
private theorem not_model27_eq3346 : Not (Equation3346 (Fin 7)) := by decideFin!
private theorem not_model27_eq3350 : Not (Equation3350 (Fin 7)) := by decideFin!
private theorem not_model27_eq3353 : Not (Equation3353 (Fin 7)) := by decideFin!
private theorem not_model27_eq3388 : Not (Equation3388 (Fin 7)) := by decideFin!
private theorem not_model27_eq3414 : Not (Equation3414 (Fin 7)) := by decideFin!
private theorem not_model27_eq4269 : Not (Equation4269 (Fin 7)) := by decideFin!
private theorem not_model27_eq4270 : Not (Equation4270 (Fin 7)) := by decideFin!
private theorem not_model27_eq4271 : Not (Equation4271 (Fin 7)) := by decideFin!
private theorem not_model27_eq4272 : Not (Equation4272 (Fin 7)) := by decideFin!
private theorem not_model27_eq4273 : Not (Equation4273 (Fin 7)) := by decideFin!
private theorem not_model27_eq4274 : Not (Equation4274 (Fin 7)) := by decideFin!
private theorem not_model27_eq4278 : Not (Equation4278 (Fin 7)) := by decideFin!
private theorem not_model27_eq4279 : Not (Equation4279 (Fin 7)) := by decideFin!
private theorem not_model27_eq4280 : Not (Equation4280 (Fin 7)) := by decideFin!
private theorem not_model27_eq4283 : Not (Equation4283 (Fin 7)) := by decideFin!
private theorem not_model27_eq4284 : Not (Equation4284 (Fin 7)) := by decideFin!
private theorem not_model27_eq4286 : Not (Equation4286 (Fin 7)) := by decideFin!
private theorem not_model27_eq4287 : Not (Equation4287 (Fin 7)) := by decideFin!
private theorem not_model27_eq4288 : Not (Equation4288 (Fin 7)) := by decideFin!
private theorem not_model27_eq4290 : Not (Equation4290 (Fin 7)) := by decideFin!
private theorem not_model27_eq4291 : Not (Equation4291 (Fin 7)) := by decideFin!
private theorem not_model27_eq4296 : Not (Equation4296 (Fin 7)) := by decideFin!
private theorem not_model27_eq4297 : Not (Equation4297 (Fin 7)) := by decideFin!
private theorem not_model27_eq4299 : Not (Equation4299 (Fin 7)) := by decideFin!
private theorem not_model27_eq4300 : Not (Equation4300 (Fin 7)) := by decideFin!
private theorem not_model27_eq4301 : Not (Equation4301 (Fin 7)) := by decideFin!
private theorem not_model27_eq4304 : Not (Equation4304 (Fin 7)) := by decideFin!
private theorem not_model27_eq4305 : Not (Equation4305 (Fin 7)) := by decideFin!
private theorem not_model27_eq4314 : Not (Equation4314 (Fin 7)) := by decideFin!
private theorem not_model27_eq4315 : Not (Equation4315 (Fin 7)) := by decideFin!
private theorem not_model27_eq4318 : Not (Equation4318 (Fin 7)) := by decideFin!
private theorem not_model27_eq4321 : Not (Equation4321 (Fin 7)) := by decideFin!
private theorem not_model27_eq4325 : Not (Equation4325 (Fin 7)) := by decideFin!
private theorem not_model27_eq4327 : Not (Equation4327 (Fin 7)) := by decideFin!
private theorem not_model27_eq4331 : Not (Equation4331 (Fin 7)) := by decideFin!
private theorem not_model27_eq4343 : Not (Equation4343 (Fin 7)) := by decideFin!
private theorem not_model27_eq4358 : Not (Equation4358 (Fin 7)) := by decideFin!
private theorem not_model27_eq4364 : Not (Equation4364 (Fin 7)) := by decideFin!
private theorem not_model27_eq4369 : Not (Equation4369 (Fin 7)) := by decideFin!

theorem model27_at1 : AssociativeTheory1 (Fin 7) :=
  model27_eq4512

theorem not_model27_at2 : Not (AssociativeTheory2 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq2

theorem not_model27_at3 : Not (AssociativeTheory3 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3

theorem not_model27_at4 : Not (AssociativeTheory4 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4

theorem not_model27_at5 : Not (AssociativeTheory5 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq5

theorem not_model27_at6 : Not (AssociativeTheory6 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at7 : Not (AssociativeTheory7 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq10

theorem not_model27_at8 : Not (AssociativeTheory8 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq11

theorem not_model27_at9 : Not (AssociativeTheory9 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq14

theorem not_model27_at10 : Not (AssociativeTheory10 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq16

theorem not_model27_at11 : Not (AssociativeTheory11 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq38

theorem not_model27_at12 : Not (AssociativeTheory12 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq39

theorem not_model27_at13 : Not (AssociativeTheory13 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq38

theorem not_model27_at14 : Not (AssociativeTheory14 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at15 : Not (AssociativeTheory15 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at16 : Not (AssociativeTheory16 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3

theorem not_model27_at17 : Not (AssociativeTheory17 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at18 : Not (AssociativeTheory18 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at19 : Not (AssociativeTheory19 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq47

theorem not_model27_at20 : Not (AssociativeTheory20 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at21 : Not (AssociativeTheory21 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq56

theorem not_model27_at22 : Not (AssociativeTheory22 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at23 : Not (AssociativeTheory23 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq75

theorem not_model27_at24 : Not (AssociativeTheory24 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq56

theorem not_model27_at25 : Not (AssociativeTheory25 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at26 : Not (AssociativeTheory26 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at27 : Not (AssociativeTheory27 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at28 : Not (AssociativeTheory28 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at29 : Not (AssociativeTheory29 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq308

theorem not_model27_at30 : Not (AssociativeTheory30 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at31 : Not (AssociativeTheory31 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at32 : Not (AssociativeTheory32 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq308

theorem not_model27_at33 : Not (AssociativeTheory33 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq310

theorem not_model27_at34 : Not (AssociativeTheory34 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq311

theorem not_model27_at35 : Not (AssociativeTheory35 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at36 : Not (AssociativeTheory36 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at37 : Not (AssociativeTheory37 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq312

theorem not_model27_at38 : Not (AssociativeTheory38 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at39 : Not (AssociativeTheory39 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq315

theorem not_model27_at40 : Not (AssociativeTheory40 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq318

theorem not_model27_at41 : Not (AssociativeTheory41 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at42 : Not (AssociativeTheory42 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at43 : Not (AssociativeTheory43 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at44 : Not (AssociativeTheory44 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq312

theorem not_model27_at45 : Not (AssociativeTheory45 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq325

theorem not_model27_at46 : Not (AssociativeTheory46 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3

theorem not_model27_at47 : Not (AssociativeTheory47 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq308

theorem not_model27_at48 : Not (AssociativeTheory48 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at49 : Not (AssociativeTheory49 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at50 : Not (AssociativeTheory50 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at51 : Not (AssociativeTheory51 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq333

theorem not_model27_at52 : Not (AssociativeTheory52 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3

theorem not_model27_at53 : Not (AssociativeTheory53 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at54 : Not (AssociativeTheory54 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq411

theorem not_model27_at55 : Not (AssociativeTheory55 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at56 : Not (AssociativeTheory56 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq419

theorem not_model27_at57 : Not (AssociativeTheory57 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq429

theorem not_model27_at58 : Not (AssociativeTheory58 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq440

theorem not_model27_at59 : Not (AssociativeTheory59 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at60 : Not (AssociativeTheory60 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq504

theorem not_model27_at61 : Not (AssociativeTheory61 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq513

theorem not_model27_at62 : Not (AssociativeTheory62 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq440

theorem not_model27_at63 : Not (AssociativeTheory63 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at64 : Not (AssociativeTheory64 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at65 : Not (AssociativeTheory65 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3255

theorem not_model27_at66 : Not (AssociativeTheory66 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at67 : Not (AssociativeTheory67 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3256

theorem not_model27_at68 : Not (AssociativeTheory68 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3258

theorem not_model27_at69 : Not (AssociativeTheory69 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at70 : Not (AssociativeTheory70 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3255

theorem not_model27_at71 : Not (AssociativeTheory71 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3259

theorem not_model27_at72 : Not (AssociativeTheory72 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3260

theorem not_model27_at73 : Not (AssociativeTheory73 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at74 : Not (AssociativeTheory74 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3261

theorem not_model27_at75 : Not (AssociativeTheory75 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3264

theorem not_model27_at76 : Not (AssociativeTheory76 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at77 : Not (AssociativeTheory77 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq308

theorem not_model27_at78 : Not (AssociativeTheory78 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq312

theorem not_model27_at79 : Not (AssociativeTheory79 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3260

theorem not_model27_at80 : Not (AssociativeTheory80 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at81 : Not (AssociativeTheory81 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3265

theorem not_model27_at82 : Not (AssociativeTheory82 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at83 : Not (AssociativeTheory83 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3260

theorem not_model27_at84 : Not (AssociativeTheory84 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at85 : Not (AssociativeTheory85 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3264

theorem not_model27_at86 : Not (AssociativeTheory86 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at87 : Not (AssociativeTheory87 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3260

theorem not_model27_at88 : Not (AssociativeTheory88 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at89 : Not (AssociativeTheory89 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at90 : Not (AssociativeTheory90 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at91 : Not (AssociativeTheory91 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at92 : Not (AssociativeTheory92 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at93 : Not (AssociativeTheory93 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at94 : Not (AssociativeTheory94 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3271

theorem not_model27_at95 : Not (AssociativeTheory95 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3274

theorem not_model27_at96 : Not (AssociativeTheory96 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3264

theorem not_model27_at97 : Not (AssociativeTheory97 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3278

theorem not_model27_at98 : Not (AssociativeTheory98 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3292

theorem not_model27_at99 : Not (AssociativeTheory99 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3264

theorem not_model27_at100 : Not (AssociativeTheory100 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3274

theorem not_model27_at101 : Not (AssociativeTheory101 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3264

theorem not_model27_at102 : Not (AssociativeTheory102 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3300

theorem not_model27_at103 : Not (AssociativeTheory103 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at104 : Not (AssociativeTheory104 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3306

theorem not_model27_at105 : Not (AssociativeTheory105 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at106 : Not (AssociativeTheory106 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at107 : Not (AssociativeTheory107 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3256

theorem not_model27_at108 : Not (AssociativeTheory108 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3261

theorem not_model27_at109 : Not (AssociativeTheory109 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3271

theorem not_model27_at110 : Not (AssociativeTheory110 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3278

theorem not_model27_at111 : Not (AssociativeTheory111 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3308

theorem not_model27_at112 : Not (AssociativeTheory112 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at113 : Not (AssociativeTheory113 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3315

theorem not_model27_at114 : Not (AssociativeTheory114 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at115 : Not (AssociativeTheory115 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3256

theorem not_model27_at116 : Not (AssociativeTheory116 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3306

theorem not_model27_at117 : Not (AssociativeTheory117 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3316

theorem not_model27_at118 : Not (AssociativeTheory118 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at119 : Not (AssociativeTheory119 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at120 : Not (AssociativeTheory120 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3319

theorem not_model27_at121 : Not (AssociativeTheory121 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3306

theorem not_model27_at122 : Not (AssociativeTheory122 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3346

theorem not_model27_at123 : Not (AssociativeTheory123 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at124 : Not (AssociativeTheory124 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3353

theorem not_model27_at125 : Not (AssociativeTheory125 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at126 : Not (AssociativeTheory126 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3319

theorem model27_at127 : AssociativeTheory127 (Fin 7) :=
  ⟨model27_eq4268, model27_eq4512⟩

theorem not_model27_at128 : Not (AssociativeTheory128 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at129 : Not (AssociativeTheory129 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at130 : Not (AssociativeTheory130 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at131 : Not (AssociativeTheory131 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at132 : Not (AssociativeTheory132 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at133 : Not (AssociativeTheory133 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at134 : Not (AssociativeTheory134 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at135 : Not (AssociativeTheory135 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at136 : Not (AssociativeTheory136 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4271

theorem not_model27_at137 : Not (AssociativeTheory137 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at138 : Not (AssociativeTheory138 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at139 : Not (AssociativeTheory139 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at140 : Not (AssociativeTheory140 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at141 : Not (AssociativeTheory141 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at142 : Not (AssociativeTheory142 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at143 : Not (AssociativeTheory143 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at144 : Not (AssociativeTheory144 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4271

theorem not_model27_at145 : Not (AssociativeTheory145 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at146 : Not (AssociativeTheory146 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at147 : Not (AssociativeTheory147 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at148 : Not (AssociativeTheory148 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at149 : Not (AssociativeTheory149 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem model27_at150 : AssociativeTheory150 (Fin 7) :=
  ⟨model27_eq4275, model27_eq4512⟩

theorem model27_at151 : AssociativeTheory151 (Fin 7) :=
  ⟨model27_eq4268, model27_eq4275, model27_eq4512⟩

theorem not_model27_at152 : Not (AssociativeTheory152 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at153 : Not (AssociativeTheory153 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at154 : Not (AssociativeTheory154 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at155 : Not (AssociativeTheory155 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at156 : Not (AssociativeTheory156 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at157 : Not (AssociativeTheory157 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem model27_at158 : AssociativeTheory158 (Fin 7) :=
  ⟨model27_eq4276, model27_eq4512⟩

theorem not_model27_at159 : Not (AssociativeTheory159 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at160 : Not (AssociativeTheory160 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4278

theorem not_model27_at161 : Not (AssociativeTheory161 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at162 : Not (AssociativeTheory162 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq47

theorem not_model27_at163 : Not (AssociativeTheory163 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq56

theorem not_model27_at164 : Not (AssociativeTheory164 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at165 : Not (AssociativeTheory165 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at166 : Not (AssociativeTheory166 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq411

theorem not_model27_at167 : Not (AssociativeTheory167 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq440

theorem not_model27_at168 : Not (AssociativeTheory168 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at169 : Not (AssociativeTheory169 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3256

theorem not_model27_at170 : Not (AssociativeTheory170 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3319

theorem not_model27_at171 : Not (AssociativeTheory171 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at172 : Not (AssociativeTheory172 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at173 : Not (AssociativeTheory173 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at174 : Not (AssociativeTheory174 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at175 : Not (AssociativeTheory175 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at176 : Not (AssociativeTheory176 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at177 : Not (AssociativeTheory177 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at178 : Not (AssociativeTheory178 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at179 : Not (AssociativeTheory179 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at180 : Not (AssociativeTheory180 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at181 : Not (AssociativeTheory181 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq43

theorem not_model27_at182 : Not (AssociativeTheory182 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at183 : Not (AssociativeTheory183 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at184 : Not (AssociativeTheory184 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at185 : Not (AssociativeTheory185 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4287

theorem not_model27_at186 : Not (AssociativeTheory186 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at187 : Not (AssociativeTheory187 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at188 : Not (AssociativeTheory188 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at189 : Not (AssociativeTheory189 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq411

theorem not_model27_at190 : Not (AssociativeTheory190 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at191 : Not (AssociativeTheory191 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at192 : Not (AssociativeTheory192 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at193 : Not (AssociativeTheory193 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at194 : Not (AssociativeTheory194 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at195 : Not (AssociativeTheory195 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at196 : Not (AssociativeTheory196 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at197 : Not (AssociativeTheory197 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at198 : Not (AssociativeTheory198 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at199 : Not (AssociativeTheory199 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at200 : Not (AssociativeTheory200 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at201 : Not (AssociativeTheory201 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at202 : Not (AssociativeTheory202 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at203 : Not (AssociativeTheory203 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at204 : Not (AssociativeTheory204 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at205 : Not (AssociativeTheory205 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at206 : Not (AssociativeTheory206 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at207 : Not (AssociativeTheory207 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq312

theorem not_model27_at208 : Not (AssociativeTheory208 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at209 : Not (AssociativeTheory209 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at210 : Not (AssociativeTheory210 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at211 : Not (AssociativeTheory211 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at212 : Not (AssociativeTheory212 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at213 : Not (AssociativeTheory213 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at214 : Not (AssociativeTheory214 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at215 : Not (AssociativeTheory215 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at216 : Not (AssociativeTheory216 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at217 : Not (AssociativeTheory217 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at218 : Not (AssociativeTheory218 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at219 : Not (AssociativeTheory219 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at220 : Not (AssociativeTheory220 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at221 : Not (AssociativeTheory221 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem model27_at222 : AssociativeTheory222 (Fin 7) :=
  ⟨model27_eq4293, model27_eq4512⟩

theorem not_model27_at223 : Not (AssociativeTheory223 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at224 : Not (AssociativeTheory224 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at225 : Not (AssociativeTheory225 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at226 : Not (AssociativeTheory226 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem model27_at227 : AssociativeTheory227 (Fin 7) :=
  ⟨model27_eq4276, model27_eq4293, model27_eq4512⟩

theorem not_model27_at228 : Not (AssociativeTheory228 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4300

theorem not_model27_at229 : Not (AssociativeTheory229 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at230 : Not (AssociativeTheory230 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at231 : Not (AssociativeTheory231 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at232 : Not (AssociativeTheory232 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq308

theorem not_model27_at233 : Not (AssociativeTheory233 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at234 : Not (AssociativeTheory234 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at235 : Not (AssociativeTheory235 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at236 : Not (AssociativeTheory236 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at237 : Not (AssociativeTheory237 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at238 : Not (AssociativeTheory238 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at239 : Not (AssociativeTheory239 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4315

theorem not_model27_at240 : Not (AssociativeTheory240 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem model27_at241 : AssociativeTheory241 (Fin 7) :=
  ⟨model27_eq4320, model27_eq4512⟩

theorem not_model27_at242 : Not (AssociativeTheory242 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq47

theorem not_model27_at243 : Not (AssociativeTheory243 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq75

theorem not_model27_at244 : Not (AssociativeTheory244 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at245 : Not (AssociativeTheory245 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at246 : Not (AssociativeTheory246 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq411

theorem not_model27_at247 : Not (AssociativeTheory247 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq513

theorem not_model27_at248 : Not (AssociativeTheory248 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at249 : Not (AssociativeTheory249 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3261

theorem not_model27_at250 : Not (AssociativeTheory250 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3306

theorem model27_at251 : AssociativeTheory251 (Fin 7) :=
  ⟨model27_eq4268, model27_eq4320, model27_eq4512⟩

theorem model27_at252 : AssociativeTheory252 (Fin 7) :=
  ⟨model27_eq4275, model27_eq4320, model27_eq4512⟩

theorem model27_at253 : AssociativeTheory253 (Fin 7) :=
  ⟨model27_eq4276, model27_eq4320, model27_eq4512⟩

theorem model27_at254 : AssociativeTheory254 (Fin 7) :=
  ⟨model27_eq4293, model27_eq4320, model27_eq4512⟩

theorem model27_at255 : AssociativeTheory255 (Fin 7) :=
  ⟨model27_eq4276, model27_eq4293, model27_eq4320, model27_eq4512⟩

theorem not_model27_at256 : Not (AssociativeTheory256 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at257 : Not (AssociativeTheory257 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at258 : Not (AssociativeTheory258 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at259 : Not (AssociativeTheory259 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at260 : Not (AssociativeTheory260 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at261 : Not (AssociativeTheory261 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at262 : Not (AssociativeTheory262 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at263 : Not (AssociativeTheory263 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at264 : Not (AssociativeTheory264 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at265 : Not (AssociativeTheory265 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at266 : Not (AssociativeTheory266 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3260

theorem not_model27_at267 : Not (AssociativeTheory267 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3265

theorem not_model27_at268 : Not (AssociativeTheory268 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3260

theorem not_model27_at269 : Not (AssociativeTheory269 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at270 : Not (AssociativeTheory270 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at271 : Not (AssociativeTheory271 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at272 : Not (AssociativeTheory272 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at273 : Not (AssociativeTheory273 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at274 : Not (AssociativeTheory274 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at275 : Not (AssociativeTheory275 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at276 : Not (AssociativeTheory276 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at277 : Not (AssociativeTheory277 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at278 : Not (AssociativeTheory278 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at279 : Not (AssociativeTheory279 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at280 : Not (AssociativeTheory280 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at281 : Not (AssociativeTheory281 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at282 : Not (AssociativeTheory282 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at283 : Not (AssociativeTheory283 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at284 : Not (AssociativeTheory284 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at285 : Not (AssociativeTheory285 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at286 : Not (AssociativeTheory286 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at287 : Not (AssociativeTheory287 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at288 : Not (AssociativeTheory288 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at289 : Not (AssociativeTheory289 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at290 : Not (AssociativeTheory290 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at291 : Not (AssociativeTheory291 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at292 : Not (AssociativeTheory292 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at293 : Not (AssociativeTheory293 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at294 : Not (AssociativeTheory294 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at295 : Not (AssociativeTheory295 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at296 : Not (AssociativeTheory296 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at297 : Not (AssociativeTheory297 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at298 : Not (AssociativeTheory298 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at299 : Not (AssociativeTheory299 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at300 : Not (AssociativeTheory300 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at301 : Not (AssociativeTheory301 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at302 : Not (AssociativeTheory302 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at303 : Not (AssociativeTheory303 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at304 : Not (AssociativeTheory304 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at305 : Not (AssociativeTheory305 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at306 : Not (AssociativeTheory306 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4358

theorem not_model27_at307 : Not (AssociativeTheory307 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3

theorem not_model27_at308 : Not (AssociativeTheory308 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at309 : Not (AssociativeTheory309 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at310 : Not (AssociativeTheory310 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq47

theorem not_model27_at311 : Not (AssociativeTheory311 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at312 : Not (AssociativeTheory312 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at313 : Not (AssociativeTheory313 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq308

theorem not_model27_at314 : Not (AssociativeTheory314 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at315 : Not (AssociativeTheory315 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at316 : Not (AssociativeTheory316 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq411

theorem not_model27_at317 : Not (AssociativeTheory317 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at318 : Not (AssociativeTheory318 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3256

theorem not_model27_at319 : Not (AssociativeTheory319 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at320 : Not (AssociativeTheory320 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at321 : Not (AssociativeTheory321 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3306

theorem not_model27_at322 : Not (AssociativeTheory322 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3319

theorem not_model27_at323 : Not (AssociativeTheory323 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4358

theorem not_model27_at324 : Not (AssociativeTheory324 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at325 : Not (AssociativeTheory325 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at326 : Not (AssociativeTheory326 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at327 : Not (AssociativeTheory327 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4272

theorem not_model27_at328 : Not (AssociativeTheory328 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at329 : Not (AssociativeTheory329 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at330 : Not (AssociativeTheory330 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at331 : Not (AssociativeTheory331 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4358

theorem not_model27_at332 : Not (AssociativeTheory332 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at333 : Not (AssociativeTheory333 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at334 : Not (AssociativeTheory334 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at335 : Not (AssociativeTheory335 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at336 : Not (AssociativeTheory336 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at337 : Not (AssociativeTheory337 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at338 : Not (AssociativeTheory338 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4290

theorem not_model27_at339 : Not (AssociativeTheory339 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at340 : Not (AssociativeTheory340 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at341 : Not (AssociativeTheory341 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at342 : Not (AssociativeTheory342 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at343 : Not (AssociativeTheory343 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at344 : Not (AssociativeTheory344 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at345 : Not (AssociativeTheory345 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at346 : Not (AssociativeTheory346 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at347 : Not (AssociativeTheory347 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at348 : Not (AssociativeTheory348 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4343

theorem not_model27_at349 : Not (AssociativeTheory349 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at350 : Not (AssociativeTheory350 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem model27_at351 : AssociativeTheory351 (Fin 7) :=
  ⟨model27_eq4362, model27_eq4512⟩

theorem not_model27_at352 : Not (AssociativeTheory352 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3

theorem not_model27_at353 : Not (AssociativeTheory353 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq8

theorem not_model27_at354 : Not (AssociativeTheory354 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at355 : Not (AssociativeTheory355 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq47

theorem not_model27_at356 : Not (AssociativeTheory356 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at357 : Not (AssociativeTheory357 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at358 : Not (AssociativeTheory358 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at359 : Not (AssociativeTheory359 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq323

theorem not_model27_at360 : Not (AssociativeTheory360 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq326

theorem not_model27_at361 : Not (AssociativeTheory361 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq411

theorem not_model27_at362 : Not (AssociativeTheory362 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at363 : Not (AssociativeTheory363 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3261

theorem not_model27_at364 : Not (AssociativeTheory364 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at365 : Not (AssociativeTheory365 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3300

theorem not_model27_at366 : Not (AssociativeTheory366 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3306

theorem not_model27_at367 : Not (AssociativeTheory367 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3319

theorem model27_at368 : AssociativeTheory368 (Fin 7) :=
  ⟨model27_eq4268, model27_eq4362, model27_eq4512⟩

theorem not_model27_at369 : Not (AssociativeTheory369 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at370 : Not (AssociativeTheory370 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at371 : Not (AssociativeTheory371 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at372 : Not (AssociativeTheory372 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem model27_at373 : AssociativeTheory373 (Fin 7) :=
  ⟨model27_eq4275, model27_eq4362, model27_eq4512⟩

theorem not_model27_at374 : Not (AssociativeTheory374 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at375 : Not (AssociativeTheory375 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem model27_at376 : AssociativeTheory376 (Fin 7) :=
  ⟨model27_eq4276, model27_eq4362, model27_eq4512⟩

theorem not_model27_at377 : Not (AssociativeTheory377 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at378 : Not (AssociativeTheory378 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at379 : Not (AssociativeTheory379 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at380 : Not (AssociativeTheory380 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at381 : Not (AssociativeTheory381 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at382 : Not (AssociativeTheory382 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at383 : Not (AssociativeTheory383 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at384 : Not (AssociativeTheory384 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at385 : Not (AssociativeTheory385 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at386 : Not (AssociativeTheory386 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem model27_at387 : AssociativeTheory387 (Fin 7) :=
  ⟨model27_eq4293, model27_eq4362, model27_eq4512⟩

theorem not_model27_at388 : Not (AssociativeTheory388 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem model27_at389 : AssociativeTheory389 (Fin 7) :=
  ⟨model27_eq4276, model27_eq4293, model27_eq4362, model27_eq4512⟩

theorem not_model27_at390 : Not (AssociativeTheory390 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at391 : Not (AssociativeTheory391 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at392 : Not (AssociativeTheory392 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at393 : Not (AssociativeTheory393 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at394 : Not (AssociativeTheory394 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at395 : Not (AssociativeTheory395 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4314

theorem not_model27_at396 : Not (AssociativeTheory396 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4358

theorem not_model27_at397 : Not (AssociativeTheory397 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at398 : Not (AssociativeTheory398 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at399 : Not (AssociativeTheory399 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at400 : Not (AssociativeTheory400 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at401 : Not (AssociativeTheory401 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at402 : Not (AssociativeTheory402 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4358

theorem not_model27_at403 : Not (AssociativeTheory403 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at404 : Not (AssociativeTheory404 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4358

theorem not_model27_at405 : Not (AssociativeTheory405 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at406 : Not (AssociativeTheory406 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at407 : Not (AssociativeTheory407 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at408 : Not (AssociativeTheory408 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4364

theorem not_model27_at409 : Not (AssociativeTheory409 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at410 : Not (AssociativeTheory410 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at411 : Not (AssociativeTheory411 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at412 : Not (AssociativeTheory412 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at413 : Not (AssociativeTheory413 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at414 : Not (AssociativeTheory414 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4364

theorem not_model27_at415 : Not (AssociativeTheory415 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at416 : Not (AssociativeTheory416 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4364

theorem not_model27_at417 : Not (AssociativeTheory417 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at418 : Not (AssociativeTheory418 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at419 : Not (AssociativeTheory419 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at420 : Not (AssociativeTheory420 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4369

theorem not_model27_at421 : Not (AssociativeTheory421 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at422 : Not (AssociativeTheory422 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at423 : Not (AssociativeTheory423 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at424 : Not (AssociativeTheory424 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at425 : Not (AssociativeTheory425 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at426 : Not (AssociativeTheory426 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at427 : Not (AssociativeTheory427 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq309

theorem not_model27_at428 : Not (AssociativeTheory428 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4369

theorem not_model27_at429 : Not (AssociativeTheory429 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at430 : Not (AssociativeTheory430 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at431 : Not (AssociativeTheory431 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at432 : Not (AssociativeTheory432 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4273

theorem not_model27_at433 : Not (AssociativeTheory433 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at434 : Not (AssociativeTheory434 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4270

theorem not_model27_at435 : Not (AssociativeTheory435 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4369

theorem not_model27_at436 : Not (AssociativeTheory436 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at437 : Not (AssociativeTheory437 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at438 : Not (AssociativeTheory438 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3253

theorem not_model27_at439 : Not (AssociativeTheory439 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at440 : Not (AssociativeTheory440 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at441 : Not (AssociativeTheory441 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at442 : Not (AssociativeTheory442 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4269

theorem not_model27_at443 : Not (AssociativeTheory443 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at444 : Not (AssociativeTheory444 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at445 : Not (AssociativeTheory445 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at446 : Not (AssociativeTheory446 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4283

theorem not_model27_at447 : Not (AssociativeTheory447 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at448 : Not (AssociativeTheory448 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4291

theorem not_model27_at449 : Not (AssociativeTheory449 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at450 : Not (AssociativeTheory450 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq40

theorem not_model27_at451 : Not (AssociativeTheory451 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq307

theorem not_model27_at452 : Not (AssociativeTheory452 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq3267

theorem not_model27_at453 : Not (AssociativeTheory453 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at454 : Not (AssociativeTheory454 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4321

theorem not_model27_at455 : Not (AssociativeTheory455 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284

theorem not_model27_at456 : Not (AssociativeTheory456 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model27_eq4284
