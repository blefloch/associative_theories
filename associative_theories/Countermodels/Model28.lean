import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model28_op := finOpTable "[[1,2,2,5,2,4,2],[2,2,2,4,2,2,2],[2,2,2,2,2,2,2],[6,4,2,2,2,2,2],[2,2,2,2,2,2,2],[2,2,2,2,2,2,2],[4,2,2,2,2,2,2]]"
private def model28 : Magma (Fin 7) where op := model28_op
private instance : Magma (Fin 7) := model28

private theorem model28_eq1 : Equation1 (Fin 7) := by decideFin!
private theorem model28_eq4269 : Equation4269 (Fin 7) := by decideFin!
private theorem model28_eq4273 : Equation4273 (Fin 7) := by decideFin!
private theorem model28_eq4276 : Equation4276 (Fin 7) := by decideFin!
private theorem model28_eq4279 : Equation4279 (Fin 7) := by decideFin!
private theorem model28_eq4290 : Equation4290 (Fin 7) := by decideFin!
private theorem model28_eq4321 : Equation4321 (Fin 7) := by decideFin!
private theorem model28_eq4369 : Equation4369 (Fin 7) := by decideFin!
private theorem model28_eq4512 : Equation4512 (Fin 7) := by decideFin!
private theorem not_model28_eq2 : Not (Equation2 (Fin 7)) := by decideFin!
private theorem not_model28_eq3 : Not (Equation3 (Fin 7)) := by decideFin!
private theorem not_model28_eq4 : Not (Equation4 (Fin 7)) := by decideFin!
private theorem not_model28_eq5 : Not (Equation5 (Fin 7)) := by decideFin!
private theorem not_model28_eq8 : Not (Equation8 (Fin 7)) := by decideFin!
private theorem not_model28_eq10 : Not (Equation10 (Fin 7)) := by decideFin!
private theorem not_model28_eq11 : Not (Equation11 (Fin 7)) := by decideFin!
private theorem not_model28_eq14 : Not (Equation14 (Fin 7)) := by decideFin!
private theorem not_model28_eq16 : Not (Equation16 (Fin 7)) := by decideFin!
private theorem not_model28_eq38 : Not (Equation38 (Fin 7)) := by decideFin!
private theorem not_model28_eq39 : Not (Equation39 (Fin 7)) := by decideFin!
private theorem not_model28_eq40 : Not (Equation40 (Fin 7)) := by decideFin!
private theorem not_model28_eq41 : Not (Equation41 (Fin 7)) := by decideFin!
private theorem not_model28_eq43 : Not (Equation43 (Fin 7)) := by decideFin!
private theorem not_model28_eq47 : Not (Equation47 (Fin 7)) := by decideFin!
private theorem not_model28_eq56 : Not (Equation56 (Fin 7)) := by decideFin!
private theorem not_model28_eq66 : Not (Equation66 (Fin 7)) := by decideFin!
private theorem not_model28_eq75 : Not (Equation75 (Fin 7)) := by decideFin!
private theorem not_model28_eq307 : Not (Equation307 (Fin 7)) := by decideFin!
private theorem not_model28_eq308 : Not (Equation308 (Fin 7)) := by decideFin!
private theorem not_model28_eq309 : Not (Equation309 (Fin 7)) := by decideFin!
private theorem not_model28_eq310 : Not (Equation310 (Fin 7)) := by decideFin!
private theorem not_model28_eq311 : Not (Equation311 (Fin 7)) := by decideFin!
private theorem not_model28_eq312 : Not (Equation312 (Fin 7)) := by decideFin!
private theorem not_model28_eq313 : Not (Equation313 (Fin 7)) := by decideFin!
private theorem not_model28_eq314 : Not (Equation314 (Fin 7)) := by decideFin!
private theorem not_model28_eq315 : Not (Equation315 (Fin 7)) := by decideFin!
private theorem not_model28_eq316 : Not (Equation316 (Fin 7)) := by decideFin!
private theorem not_model28_eq318 : Not (Equation318 (Fin 7)) := by decideFin!
private theorem not_model28_eq323 : Not (Equation323 (Fin 7)) := by decideFin!
private theorem not_model28_eq325 : Not (Equation325 (Fin 7)) := by decideFin!
private theorem not_model28_eq326 : Not (Equation326 (Fin 7)) := by decideFin!
private theorem not_model28_eq327 : Not (Equation327 (Fin 7)) := by decideFin!
private theorem not_model28_eq329 : Not (Equation329 (Fin 7)) := by decideFin!
private theorem not_model28_eq332 : Not (Equation332 (Fin 7)) := by decideFin!
private theorem not_model28_eq333 : Not (Equation333 (Fin 7)) := by decideFin!
private theorem not_model28_eq343 : Not (Equation343 (Fin 7)) := by decideFin!
private theorem not_model28_eq411 : Not (Equation411 (Fin 7)) := by decideFin!
private theorem not_model28_eq419 : Not (Equation419 (Fin 7)) := by decideFin!
private theorem not_model28_eq429 : Not (Equation429 (Fin 7)) := by decideFin!
private theorem not_model28_eq440 : Not (Equation440 (Fin 7)) := by decideFin!
private theorem not_model28_eq477 : Not (Equation477 (Fin 7)) := by decideFin!
private theorem not_model28_eq504 : Not (Equation504 (Fin 7)) := by decideFin!
private theorem not_model28_eq513 : Not (Equation513 (Fin 7)) := by decideFin!
private theorem not_model28_eq3253 : Not (Equation3253 (Fin 7)) := by decideFin!
private theorem not_model28_eq3255 : Not (Equation3255 (Fin 7)) := by decideFin!
private theorem not_model28_eq3256 : Not (Equation3256 (Fin 7)) := by decideFin!
private theorem not_model28_eq3258 : Not (Equation3258 (Fin 7)) := by decideFin!
private theorem not_model28_eq3259 : Not (Equation3259 (Fin 7)) := by decideFin!
private theorem not_model28_eq3260 : Not (Equation3260 (Fin 7)) := by decideFin!
private theorem not_model28_eq3261 : Not (Equation3261 (Fin 7)) := by decideFin!
private theorem not_model28_eq3264 : Not (Equation3264 (Fin 7)) := by decideFin!
private theorem not_model28_eq3265 : Not (Equation3265 (Fin 7)) := by decideFin!
private theorem not_model28_eq3267 : Not (Equation3267 (Fin 7)) := by decideFin!
private theorem not_model28_eq3271 : Not (Equation3271 (Fin 7)) := by decideFin!
private theorem not_model28_eq3273 : Not (Equation3273 (Fin 7)) := by decideFin!
private theorem not_model28_eq3274 : Not (Equation3274 (Fin 7)) := by decideFin!
private theorem not_model28_eq3275 : Not (Equation3275 (Fin 7)) := by decideFin!
private theorem not_model28_eq3277 : Not (Equation3277 (Fin 7)) := by decideFin!
private theorem not_model28_eq3278 : Not (Equation3278 (Fin 7)) := by decideFin!
private theorem not_model28_eq3290 : Not (Equation3290 (Fin 7)) := by decideFin!
private theorem not_model28_eq3292 : Not (Equation3292 (Fin 7)) := by decideFin!
private theorem not_model28_eq3300 : Not (Equation3300 (Fin 7)) := by decideFin!
private theorem not_model28_eq3306 : Not (Equation3306 (Fin 7)) := by decideFin!
private theorem not_model28_eq3308 : Not (Equation3308 (Fin 7)) := by decideFin!
private theorem not_model28_eq3309 : Not (Equation3309 (Fin 7)) := by decideFin!
private theorem not_model28_eq3315 : Not (Equation3315 (Fin 7)) := by decideFin!
private theorem not_model28_eq3316 : Not (Equation3316 (Fin 7)) := by decideFin!
private theorem not_model28_eq3319 : Not (Equation3319 (Fin 7)) := by decideFin!
private theorem not_model28_eq3322 : Not (Equation3322 (Fin 7)) := by decideFin!
private theorem not_model28_eq3323 : Not (Equation3323 (Fin 7)) := by decideFin!
private theorem not_model28_eq3326 : Not (Equation3326 (Fin 7)) := by decideFin!
private theorem not_model28_eq3331 : Not (Equation3331 (Fin 7)) := by decideFin!
private theorem not_model28_eq3334 : Not (Equation3334 (Fin 7)) := by decideFin!
private theorem not_model28_eq3342 : Not (Equation3342 (Fin 7)) := by decideFin!
private theorem not_model28_eq3346 : Not (Equation3346 (Fin 7)) := by decideFin!
private theorem not_model28_eq3350 : Not (Equation3350 (Fin 7)) := by decideFin!
private theorem not_model28_eq3353 : Not (Equation3353 (Fin 7)) := by decideFin!
private theorem not_model28_eq3388 : Not (Equation3388 (Fin 7)) := by decideFin!
private theorem not_model28_eq3414 : Not (Equation3414 (Fin 7)) := by decideFin!
private theorem not_model28_eq4268 : Not (Equation4268 (Fin 7)) := by decideFin!
private theorem not_model28_eq4270 : Not (Equation4270 (Fin 7)) := by decideFin!
private theorem not_model28_eq4271 : Not (Equation4271 (Fin 7)) := by decideFin!
private theorem not_model28_eq4272 : Not (Equation4272 (Fin 7)) := by decideFin!
private theorem not_model28_eq4274 : Not (Equation4274 (Fin 7)) := by decideFin!
private theorem not_model28_eq4275 : Not (Equation4275 (Fin 7)) := by decideFin!
private theorem not_model28_eq4277 : Not (Equation4277 (Fin 7)) := by decideFin!
private theorem not_model28_eq4278 : Not (Equation4278 (Fin 7)) := by decideFin!
private theorem not_model28_eq4280 : Not (Equation4280 (Fin 7)) := by decideFin!
private theorem not_model28_eq4283 : Not (Equation4283 (Fin 7)) := by decideFin!
private theorem not_model28_eq4284 : Not (Equation4284 (Fin 7)) := by decideFin!
private theorem not_model28_eq4286 : Not (Equation4286 (Fin 7)) := by decideFin!
private theorem not_model28_eq4287 : Not (Equation4287 (Fin 7)) := by decideFin!
private theorem not_model28_eq4288 : Not (Equation4288 (Fin 7)) := by decideFin!
private theorem not_model28_eq4291 : Not (Equation4291 (Fin 7)) := by decideFin!
private theorem not_model28_eq4293 : Not (Equation4293 (Fin 7)) := by decideFin!
private theorem not_model28_eq4296 : Not (Equation4296 (Fin 7)) := by decideFin!
private theorem not_model28_eq4297 : Not (Equation4297 (Fin 7)) := by decideFin!
private theorem not_model28_eq4299 : Not (Equation4299 (Fin 7)) := by decideFin!
private theorem not_model28_eq4300 : Not (Equation4300 (Fin 7)) := by decideFin!
private theorem not_model28_eq4301 : Not (Equation4301 (Fin 7)) := by decideFin!
private theorem not_model28_eq4304 : Not (Equation4304 (Fin 7)) := by decideFin!
private theorem not_model28_eq4305 : Not (Equation4305 (Fin 7)) := by decideFin!
private theorem not_model28_eq4314 : Not (Equation4314 (Fin 7)) := by decideFin!
private theorem not_model28_eq4315 : Not (Equation4315 (Fin 7)) := by decideFin!
private theorem not_model28_eq4318 : Not (Equation4318 (Fin 7)) := by decideFin!
private theorem not_model28_eq4320 : Not (Equation4320 (Fin 7)) := by decideFin!
private theorem not_model28_eq4325 : Not (Equation4325 (Fin 7)) := by decideFin!
private theorem not_model28_eq4327 : Not (Equation4327 (Fin 7)) := by decideFin!
private theorem not_model28_eq4331 : Not (Equation4331 (Fin 7)) := by decideFin!
private theorem not_model28_eq4343 : Not (Equation4343 (Fin 7)) := by decideFin!
private theorem not_model28_eq4358 : Not (Equation4358 (Fin 7)) := by decideFin!
private theorem not_model28_eq4362 : Not (Equation4362 (Fin 7)) := by decideFin!
private theorem not_model28_eq4364 : Not (Equation4364 (Fin 7)) := by decideFin!

theorem model28_at1 : AssociativeTheory1 (Fin 7) :=
  model28_eq4512

theorem not_model28_at2 : Not (AssociativeTheory2 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq2

theorem not_model28_at3 : Not (AssociativeTheory3 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3

theorem not_model28_at4 : Not (AssociativeTheory4 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4

theorem not_model28_at5 : Not (AssociativeTheory5 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq5

theorem not_model28_at6 : Not (AssociativeTheory6 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at7 : Not (AssociativeTheory7 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq10

theorem not_model28_at8 : Not (AssociativeTheory8 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq11

theorem not_model28_at9 : Not (AssociativeTheory9 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq14

theorem not_model28_at10 : Not (AssociativeTheory10 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq16

theorem not_model28_at11 : Not (AssociativeTheory11 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq38

theorem not_model28_at12 : Not (AssociativeTheory12 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq39

theorem not_model28_at13 : Not (AssociativeTheory13 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq38

theorem not_model28_at14 : Not (AssociativeTheory14 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at15 : Not (AssociativeTheory15 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at16 : Not (AssociativeTheory16 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3

theorem not_model28_at17 : Not (AssociativeTheory17 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at18 : Not (AssociativeTheory18 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at19 : Not (AssociativeTheory19 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq47

theorem not_model28_at20 : Not (AssociativeTheory20 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at21 : Not (AssociativeTheory21 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq56

theorem not_model28_at22 : Not (AssociativeTheory22 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at23 : Not (AssociativeTheory23 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq75

theorem not_model28_at24 : Not (AssociativeTheory24 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq56

theorem not_model28_at25 : Not (AssociativeTheory25 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at26 : Not (AssociativeTheory26 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at27 : Not (AssociativeTheory27 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at28 : Not (AssociativeTheory28 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at29 : Not (AssociativeTheory29 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq308

theorem not_model28_at30 : Not (AssociativeTheory30 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at31 : Not (AssociativeTheory31 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at32 : Not (AssociativeTheory32 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq308

theorem not_model28_at33 : Not (AssociativeTheory33 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq310

theorem not_model28_at34 : Not (AssociativeTheory34 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq311

theorem not_model28_at35 : Not (AssociativeTheory35 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at36 : Not (AssociativeTheory36 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at37 : Not (AssociativeTheory37 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq312

theorem not_model28_at38 : Not (AssociativeTheory38 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at39 : Not (AssociativeTheory39 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq315

theorem not_model28_at40 : Not (AssociativeTheory40 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq318

theorem not_model28_at41 : Not (AssociativeTheory41 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at42 : Not (AssociativeTheory42 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at43 : Not (AssociativeTheory43 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at44 : Not (AssociativeTheory44 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq312

theorem not_model28_at45 : Not (AssociativeTheory45 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq325

theorem not_model28_at46 : Not (AssociativeTheory46 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3

theorem not_model28_at47 : Not (AssociativeTheory47 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq308

theorem not_model28_at48 : Not (AssociativeTheory48 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at49 : Not (AssociativeTheory49 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at50 : Not (AssociativeTheory50 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at51 : Not (AssociativeTheory51 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq333

theorem not_model28_at52 : Not (AssociativeTheory52 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3

theorem not_model28_at53 : Not (AssociativeTheory53 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at54 : Not (AssociativeTheory54 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq411

theorem not_model28_at55 : Not (AssociativeTheory55 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at56 : Not (AssociativeTheory56 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq419

theorem not_model28_at57 : Not (AssociativeTheory57 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq429

theorem not_model28_at58 : Not (AssociativeTheory58 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq440

theorem not_model28_at59 : Not (AssociativeTheory59 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at60 : Not (AssociativeTheory60 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq504

theorem not_model28_at61 : Not (AssociativeTheory61 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq513

theorem not_model28_at62 : Not (AssociativeTheory62 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq440

theorem not_model28_at63 : Not (AssociativeTheory63 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at64 : Not (AssociativeTheory64 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at65 : Not (AssociativeTheory65 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3255

theorem not_model28_at66 : Not (AssociativeTheory66 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at67 : Not (AssociativeTheory67 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3256

theorem not_model28_at68 : Not (AssociativeTheory68 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3258

theorem not_model28_at69 : Not (AssociativeTheory69 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at70 : Not (AssociativeTheory70 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3255

theorem not_model28_at71 : Not (AssociativeTheory71 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3259

theorem not_model28_at72 : Not (AssociativeTheory72 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3260

theorem not_model28_at73 : Not (AssociativeTheory73 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at74 : Not (AssociativeTheory74 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3261

theorem not_model28_at75 : Not (AssociativeTheory75 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3264

theorem not_model28_at76 : Not (AssociativeTheory76 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at77 : Not (AssociativeTheory77 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq308

theorem not_model28_at78 : Not (AssociativeTheory78 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq312

theorem not_model28_at79 : Not (AssociativeTheory79 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3260

theorem not_model28_at80 : Not (AssociativeTheory80 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at81 : Not (AssociativeTheory81 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3265

theorem not_model28_at82 : Not (AssociativeTheory82 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at83 : Not (AssociativeTheory83 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3260

theorem not_model28_at84 : Not (AssociativeTheory84 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at85 : Not (AssociativeTheory85 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3264

theorem not_model28_at86 : Not (AssociativeTheory86 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at87 : Not (AssociativeTheory87 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3260

theorem not_model28_at88 : Not (AssociativeTheory88 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at89 : Not (AssociativeTheory89 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at90 : Not (AssociativeTheory90 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at91 : Not (AssociativeTheory91 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at92 : Not (AssociativeTheory92 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at93 : Not (AssociativeTheory93 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at94 : Not (AssociativeTheory94 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3271

theorem not_model28_at95 : Not (AssociativeTheory95 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3274

theorem not_model28_at96 : Not (AssociativeTheory96 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3264

theorem not_model28_at97 : Not (AssociativeTheory97 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3278

theorem not_model28_at98 : Not (AssociativeTheory98 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3292

theorem not_model28_at99 : Not (AssociativeTheory99 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3264

theorem not_model28_at100 : Not (AssociativeTheory100 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3274

theorem not_model28_at101 : Not (AssociativeTheory101 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3264

theorem not_model28_at102 : Not (AssociativeTheory102 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3300

theorem not_model28_at103 : Not (AssociativeTheory103 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at104 : Not (AssociativeTheory104 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3306

theorem not_model28_at105 : Not (AssociativeTheory105 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at106 : Not (AssociativeTheory106 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at107 : Not (AssociativeTheory107 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3256

theorem not_model28_at108 : Not (AssociativeTheory108 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3261

theorem not_model28_at109 : Not (AssociativeTheory109 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3271

theorem not_model28_at110 : Not (AssociativeTheory110 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3278

theorem not_model28_at111 : Not (AssociativeTheory111 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3308

theorem not_model28_at112 : Not (AssociativeTheory112 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at113 : Not (AssociativeTheory113 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3315

theorem not_model28_at114 : Not (AssociativeTheory114 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at115 : Not (AssociativeTheory115 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3256

theorem not_model28_at116 : Not (AssociativeTheory116 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3306

theorem not_model28_at117 : Not (AssociativeTheory117 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3316

theorem not_model28_at118 : Not (AssociativeTheory118 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at119 : Not (AssociativeTheory119 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at120 : Not (AssociativeTheory120 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3319

theorem not_model28_at121 : Not (AssociativeTheory121 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3306

theorem not_model28_at122 : Not (AssociativeTheory122 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3346

theorem not_model28_at123 : Not (AssociativeTheory123 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at124 : Not (AssociativeTheory124 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3353

theorem not_model28_at125 : Not (AssociativeTheory125 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at126 : Not (AssociativeTheory126 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3319

theorem not_model28_at127 : Not (AssociativeTheory127 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at128 : Not (AssociativeTheory128 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem model28_at129 : AssociativeTheory129 (Fin 7) :=
  ⟨model28_eq4269, model28_eq4512⟩

theorem not_model28_at130 : Not (AssociativeTheory130 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at131 : Not (AssociativeTheory131 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at132 : Not (AssociativeTheory132 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at133 : Not (AssociativeTheory133 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at134 : Not (AssociativeTheory134 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at135 : Not (AssociativeTheory135 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at136 : Not (AssociativeTheory136 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4271

theorem not_model28_at137 : Not (AssociativeTheory137 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at138 : Not (AssociativeTheory138 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at139 : Not (AssociativeTheory139 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at140 : Not (AssociativeTheory140 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at141 : Not (AssociativeTheory141 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at142 : Not (AssociativeTheory142 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at143 : Not (AssociativeTheory143 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at144 : Not (AssociativeTheory144 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4271

theorem model28_at145 : AssociativeTheory145 (Fin 7) :=
  ⟨model28_eq4273, model28_eq4512⟩

theorem not_model28_at146 : Not (AssociativeTheory146 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at147 : Not (AssociativeTheory147 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem model28_at148 : AssociativeTheory148 (Fin 7) :=
  ⟨model28_eq4269, model28_eq4273, model28_eq4512⟩

theorem not_model28_at149 : Not (AssociativeTheory149 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at150 : Not (AssociativeTheory150 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at151 : Not (AssociativeTheory151 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at152 : Not (AssociativeTheory152 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at153 : Not (AssociativeTheory153 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at154 : Not (AssociativeTheory154 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at155 : Not (AssociativeTheory155 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at156 : Not (AssociativeTheory156 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at157 : Not (AssociativeTheory157 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem model28_at158 : AssociativeTheory158 (Fin 7) :=
  ⟨model28_eq4276, model28_eq4512⟩

theorem not_model28_at159 : Not (AssociativeTheory159 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at160 : Not (AssociativeTheory160 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4278

theorem not_model28_at161 : Not (AssociativeTheory161 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at162 : Not (AssociativeTheory162 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq47

theorem not_model28_at163 : Not (AssociativeTheory163 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq56

theorem not_model28_at164 : Not (AssociativeTheory164 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at165 : Not (AssociativeTheory165 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at166 : Not (AssociativeTheory166 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq411

theorem not_model28_at167 : Not (AssociativeTheory167 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq440

theorem not_model28_at168 : Not (AssociativeTheory168 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at169 : Not (AssociativeTheory169 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3256

theorem not_model28_at170 : Not (AssociativeTheory170 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3319

theorem not_model28_at171 : Not (AssociativeTheory171 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at172 : Not (AssociativeTheory172 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at173 : Not (AssociativeTheory173 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at174 : Not (AssociativeTheory174 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at175 : Not (AssociativeTheory175 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at176 : Not (AssociativeTheory176 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at177 : Not (AssociativeTheory177 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at178 : Not (AssociativeTheory178 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at179 : Not (AssociativeTheory179 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at180 : Not (AssociativeTheory180 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at181 : Not (AssociativeTheory181 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq43

theorem not_model28_at182 : Not (AssociativeTheory182 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at183 : Not (AssociativeTheory183 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at184 : Not (AssociativeTheory184 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at185 : Not (AssociativeTheory185 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4287

theorem not_model28_at186 : Not (AssociativeTheory186 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem model28_at187 : AssociativeTheory187 (Fin 7) :=
  ⟨model28_eq4290, model28_eq4512⟩

theorem not_model28_at188 : Not (AssociativeTheory188 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at189 : Not (AssociativeTheory189 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq411

theorem not_model28_at190 : Not (AssociativeTheory190 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem model28_at191 : AssociativeTheory191 (Fin 7) :=
  ⟨model28_eq4269, model28_eq4290, model28_eq4512⟩

theorem model28_at192 : AssociativeTheory192 (Fin 7) :=
  ⟨model28_eq4273, model28_eq4290, model28_eq4512⟩

theorem model28_at193 : AssociativeTheory193 (Fin 7) :=
  ⟨model28_eq4276, model28_eq4290, model28_eq4512⟩

theorem not_model28_at194 : Not (AssociativeTheory194 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at195 : Not (AssociativeTheory195 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at196 : Not (AssociativeTheory196 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at197 : Not (AssociativeTheory197 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at198 : Not (AssociativeTheory198 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at199 : Not (AssociativeTheory199 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at200 : Not (AssociativeTheory200 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at201 : Not (AssociativeTheory201 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at202 : Not (AssociativeTheory202 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at203 : Not (AssociativeTheory203 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at204 : Not (AssociativeTheory204 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at205 : Not (AssociativeTheory205 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at206 : Not (AssociativeTheory206 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at207 : Not (AssociativeTheory207 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq312

theorem not_model28_at208 : Not (AssociativeTheory208 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at209 : Not (AssociativeTheory209 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at210 : Not (AssociativeTheory210 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at211 : Not (AssociativeTheory211 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at212 : Not (AssociativeTheory212 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at213 : Not (AssociativeTheory213 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at214 : Not (AssociativeTheory214 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at215 : Not (AssociativeTheory215 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at216 : Not (AssociativeTheory216 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at217 : Not (AssociativeTheory217 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at218 : Not (AssociativeTheory218 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at219 : Not (AssociativeTheory219 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at220 : Not (AssociativeTheory220 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at221 : Not (AssociativeTheory221 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at222 : Not (AssociativeTheory222 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at223 : Not (AssociativeTheory223 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at224 : Not (AssociativeTheory224 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at225 : Not (AssociativeTheory225 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at226 : Not (AssociativeTheory226 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at227 : Not (AssociativeTheory227 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at228 : Not (AssociativeTheory228 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4300

theorem not_model28_at229 : Not (AssociativeTheory229 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at230 : Not (AssociativeTheory230 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4314

theorem not_model28_at231 : Not (AssociativeTheory231 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at232 : Not (AssociativeTheory232 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq308

theorem not_model28_at233 : Not (AssociativeTheory233 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at234 : Not (AssociativeTheory234 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at235 : Not (AssociativeTheory235 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at236 : Not (AssociativeTheory236 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4314

theorem not_model28_at237 : Not (AssociativeTheory237 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at238 : Not (AssociativeTheory238 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at239 : Not (AssociativeTheory239 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4315

theorem not_model28_at240 : Not (AssociativeTheory240 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at241 : Not (AssociativeTheory241 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4320

theorem not_model28_at242 : Not (AssociativeTheory242 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq47

theorem not_model28_at243 : Not (AssociativeTheory243 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq75

theorem not_model28_at244 : Not (AssociativeTheory244 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at245 : Not (AssociativeTheory245 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at246 : Not (AssociativeTheory246 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq411

theorem not_model28_at247 : Not (AssociativeTheory247 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq513

theorem not_model28_at248 : Not (AssociativeTheory248 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at249 : Not (AssociativeTheory249 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3261

theorem not_model28_at250 : Not (AssociativeTheory250 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3306

theorem not_model28_at251 : Not (AssociativeTheory251 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at252 : Not (AssociativeTheory252 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at253 : Not (AssociativeTheory253 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4320

theorem not_model28_at254 : Not (AssociativeTheory254 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at255 : Not (AssociativeTheory255 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at256 : Not (AssociativeTheory256 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4314

theorem not_model28_at257 : Not (AssociativeTheory257 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at258 : Not (AssociativeTheory258 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at259 : Not (AssociativeTheory259 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at260 : Not (AssociativeTheory260 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4314

theorem not_model28_at261 : Not (AssociativeTheory261 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at262 : Not (AssociativeTheory262 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem model28_at263 : AssociativeTheory263 (Fin 7) :=
  ⟨model28_eq4321, model28_eq4512⟩

theorem not_model28_at264 : Not (AssociativeTheory264 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at265 : Not (AssociativeTheory265 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at266 : Not (AssociativeTheory266 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3260

theorem not_model28_at267 : Not (AssociativeTheory267 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3265

theorem not_model28_at268 : Not (AssociativeTheory268 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3260

theorem not_model28_at269 : Not (AssociativeTheory269 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at270 : Not (AssociativeTheory270 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at271 : Not (AssociativeTheory271 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at272 : Not (AssociativeTheory272 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem model28_at273 : AssociativeTheory273 (Fin 7) :=
  ⟨model28_eq4276, model28_eq4321, model28_eq4512⟩

theorem not_model28_at274 : Not (AssociativeTheory274 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at275 : Not (AssociativeTheory275 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at276 : Not (AssociativeTheory276 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem model28_at277 : AssociativeTheory277 (Fin 7) :=
  ⟨model28_eq4290, model28_eq4321, model28_eq4512⟩

theorem model28_at278 : AssociativeTheory278 (Fin 7) :=
  ⟨model28_eq4276, model28_eq4290, model28_eq4321, model28_eq4512⟩

theorem not_model28_at279 : Not (AssociativeTheory279 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at280 : Not (AssociativeTheory280 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at281 : Not (AssociativeTheory281 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at282 : Not (AssociativeTheory282 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at283 : Not (AssociativeTheory283 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at284 : Not (AssociativeTheory284 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at285 : Not (AssociativeTheory285 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at286 : Not (AssociativeTheory286 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at287 : Not (AssociativeTheory287 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at288 : Not (AssociativeTheory288 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at289 : Not (AssociativeTheory289 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at290 : Not (AssociativeTheory290 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at291 : Not (AssociativeTheory291 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at292 : Not (AssociativeTheory292 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at293 : Not (AssociativeTheory293 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at294 : Not (AssociativeTheory294 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at295 : Not (AssociativeTheory295 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at296 : Not (AssociativeTheory296 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at297 : Not (AssociativeTheory297 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at298 : Not (AssociativeTheory298 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at299 : Not (AssociativeTheory299 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at300 : Not (AssociativeTheory300 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at301 : Not (AssociativeTheory301 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at302 : Not (AssociativeTheory302 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at303 : Not (AssociativeTheory303 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at304 : Not (AssociativeTheory304 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at305 : Not (AssociativeTheory305 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at306 : Not (AssociativeTheory306 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at307 : Not (AssociativeTheory307 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3

theorem not_model28_at308 : Not (AssociativeTheory308 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at309 : Not (AssociativeTheory309 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at310 : Not (AssociativeTheory310 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq47

theorem not_model28_at311 : Not (AssociativeTheory311 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at312 : Not (AssociativeTheory312 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at313 : Not (AssociativeTheory313 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq308

theorem not_model28_at314 : Not (AssociativeTheory314 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at315 : Not (AssociativeTheory315 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at316 : Not (AssociativeTheory316 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq411

theorem not_model28_at317 : Not (AssociativeTheory317 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at318 : Not (AssociativeTheory318 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3256

theorem not_model28_at319 : Not (AssociativeTheory319 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at320 : Not (AssociativeTheory320 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at321 : Not (AssociativeTheory321 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3306

theorem not_model28_at322 : Not (AssociativeTheory322 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3319

theorem not_model28_at323 : Not (AssociativeTheory323 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at324 : Not (AssociativeTheory324 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at325 : Not (AssociativeTheory325 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at326 : Not (AssociativeTheory326 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4272

theorem not_model28_at327 : Not (AssociativeTheory327 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at328 : Not (AssociativeTheory328 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at329 : Not (AssociativeTheory329 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at330 : Not (AssociativeTheory330 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at331 : Not (AssociativeTheory331 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at332 : Not (AssociativeTheory332 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at333 : Not (AssociativeTheory333 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at334 : Not (AssociativeTheory334 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at335 : Not (AssociativeTheory335 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at336 : Not (AssociativeTheory336 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at337 : Not (AssociativeTheory337 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at338 : Not (AssociativeTheory338 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at339 : Not (AssociativeTheory339 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at340 : Not (AssociativeTheory340 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at341 : Not (AssociativeTheory341 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at342 : Not (AssociativeTheory342 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at343 : Not (AssociativeTheory343 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at344 : Not (AssociativeTheory344 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at345 : Not (AssociativeTheory345 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at346 : Not (AssociativeTheory346 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at347 : Not (AssociativeTheory347 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at348 : Not (AssociativeTheory348 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4343

theorem not_model28_at349 : Not (AssociativeTheory349 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at350 : Not (AssociativeTheory350 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at351 : Not (AssociativeTheory351 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4362

theorem not_model28_at352 : Not (AssociativeTheory352 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3

theorem not_model28_at353 : Not (AssociativeTheory353 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq8

theorem not_model28_at354 : Not (AssociativeTheory354 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at355 : Not (AssociativeTheory355 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq47

theorem not_model28_at356 : Not (AssociativeTheory356 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at357 : Not (AssociativeTheory357 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at358 : Not (AssociativeTheory358 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at359 : Not (AssociativeTheory359 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq323

theorem not_model28_at360 : Not (AssociativeTheory360 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq326

theorem not_model28_at361 : Not (AssociativeTheory361 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq411

theorem not_model28_at362 : Not (AssociativeTheory362 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at363 : Not (AssociativeTheory363 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3261

theorem not_model28_at364 : Not (AssociativeTheory364 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at365 : Not (AssociativeTheory365 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3300

theorem not_model28_at366 : Not (AssociativeTheory366 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3306

theorem not_model28_at367 : Not (AssociativeTheory367 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3319

theorem not_model28_at368 : Not (AssociativeTheory368 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at369 : Not (AssociativeTheory369 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4362

theorem not_model28_at370 : Not (AssociativeTheory370 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at371 : Not (AssociativeTheory371 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at372 : Not (AssociativeTheory372 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at373 : Not (AssociativeTheory373 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at374 : Not (AssociativeTheory374 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4275

theorem not_model28_at375 : Not (AssociativeTheory375 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at376 : Not (AssociativeTheory376 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4362

theorem not_model28_at377 : Not (AssociativeTheory377 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at378 : Not (AssociativeTheory378 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at379 : Not (AssociativeTheory379 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at380 : Not (AssociativeTheory380 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at381 : Not (AssociativeTheory381 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at382 : Not (AssociativeTheory382 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at383 : Not (AssociativeTheory383 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at384 : Not (AssociativeTheory384 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at385 : Not (AssociativeTheory385 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at386 : Not (AssociativeTheory386 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at387 : Not (AssociativeTheory387 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at388 : Not (AssociativeTheory388 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at389 : Not (AssociativeTheory389 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at390 : Not (AssociativeTheory390 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4314

theorem not_model28_at391 : Not (AssociativeTheory391 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at392 : Not (AssociativeTheory392 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at393 : Not (AssociativeTheory393 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4314

theorem not_model28_at394 : Not (AssociativeTheory394 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at395 : Not (AssociativeTheory395 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4293

theorem not_model28_at396 : Not (AssociativeTheory396 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at397 : Not (AssociativeTheory397 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at398 : Not (AssociativeTheory398 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at399 : Not (AssociativeTheory399 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at400 : Not (AssociativeTheory400 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at401 : Not (AssociativeTheory401 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at402 : Not (AssociativeTheory402 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at403 : Not (AssociativeTheory403 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at404 : Not (AssociativeTheory404 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4358

theorem not_model28_at405 : Not (AssociativeTheory405 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at406 : Not (AssociativeTheory406 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at407 : Not (AssociativeTheory407 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at408 : Not (AssociativeTheory408 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4364

theorem not_model28_at409 : Not (AssociativeTheory409 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at410 : Not (AssociativeTheory410 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at411 : Not (AssociativeTheory411 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at412 : Not (AssociativeTheory412 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at413 : Not (AssociativeTheory413 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at414 : Not (AssociativeTheory414 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at415 : Not (AssociativeTheory415 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem not_model28_at416 : Not (AssociativeTheory416 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4364

theorem not_model28_at417 : Not (AssociativeTheory417 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at418 : Not (AssociativeTheory418 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at419 : Not (AssociativeTheory419 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem model28_at420 : AssociativeTheory420 (Fin 7) :=
  ⟨model28_eq4369, model28_eq4512⟩

theorem not_model28_at421 : Not (AssociativeTheory421 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at422 : Not (AssociativeTheory422 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at423 : Not (AssociativeTheory423 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at424 : Not (AssociativeTheory424 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at425 : Not (AssociativeTheory425 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at426 : Not (AssociativeTheory426 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at427 : Not (AssociativeTheory427 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq309

theorem not_model28_at428 : Not (AssociativeTheory428 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem model28_at429 : AssociativeTheory429 (Fin 7) :=
  ⟨model28_eq4269, model28_eq4369, model28_eq4512⟩

theorem not_model28_at430 : Not (AssociativeTheory430 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem not_model28_at431 : Not (AssociativeTheory431 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem model28_at432 : AssociativeTheory432 (Fin 7) :=
  ⟨model28_eq4273, model28_eq4369, model28_eq4512⟩

theorem not_model28_at433 : Not (AssociativeTheory433 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at434 : Not (AssociativeTheory434 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4270

theorem model28_at435 : AssociativeTheory435 (Fin 7) :=
  ⟨model28_eq4276, model28_eq4369, model28_eq4512⟩

theorem not_model28_at436 : Not (AssociativeTheory436 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at437 : Not (AssociativeTheory437 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at438 : Not (AssociativeTheory438 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3253

theorem not_model28_at439 : Not (AssociativeTheory439 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at440 : Not (AssociativeTheory440 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at441 : Not (AssociativeTheory441 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at442 : Not (AssociativeTheory442 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at443 : Not (AssociativeTheory443 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at444 : Not (AssociativeTheory444 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at445 : Not (AssociativeTheory445 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at446 : Not (AssociativeTheory446 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4283

theorem not_model28_at447 : Not (AssociativeTheory447 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem not_model28_at448 : Not (AssociativeTheory448 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4291

theorem model28_at449 : AssociativeTheory449 (Fin 7) :=
  ⟨model28_eq4321, model28_eq4369, model28_eq4512⟩

theorem not_model28_at450 : Not (AssociativeTheory450 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq40

theorem not_model28_at451 : Not (AssociativeTheory451 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq307

theorem not_model28_at452 : Not (AssociativeTheory452 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq3267

theorem not_model28_at453 : Not (AssociativeTheory453 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4268

theorem model28_at454 : AssociativeTheory454 (Fin 7) :=
  ⟨model28_eq4276, model28_eq4321, model28_eq4369, model28_eq4512⟩

theorem not_model28_at455 : Not (AssociativeTheory455 (Fin 7)) := by
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284

theorem not_model28_at456 : Not (AssociativeTheory456 (Fin 7)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model28_eq4284
