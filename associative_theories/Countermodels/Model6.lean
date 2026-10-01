import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model6_op := finOpTable "[[0,0,0],[0,0,0],[0,0,1]]"
private def model6 : Magma (Fin 3) where op := model6_op
private instance : Magma (Fin 3) := model6

private theorem model6_eq1 : Equation1 (Fin 3) := by decideFin!
private theorem not_model6_eq2 : Not (Equation2 (Fin 3)) := by decideFin!
private theorem not_model6_eq3 : Not (Equation3 (Fin 3)) := by decideFin!
private theorem not_model6_eq4 : Not (Equation4 (Fin 3)) := by decideFin!
private theorem not_model6_eq5 : Not (Equation5 (Fin 3)) := by decideFin!
private theorem not_model6_eq8 : Not (Equation8 (Fin 3)) := by decideFin!
private theorem not_model6_eq10 : Not (Equation10 (Fin 3)) := by decideFin!
private theorem not_model6_eq11 : Not (Equation11 (Fin 3)) := by decideFin!
private theorem not_model6_eq14 : Not (Equation14 (Fin 3)) := by decideFin!
private theorem not_model6_eq16 : Not (Equation16 (Fin 3)) := by decideFin!
private theorem not_model6_eq38 : Not (Equation38 (Fin 3)) := by decideFin!
private theorem not_model6_eq39 : Not (Equation39 (Fin 3)) := by decideFin!
private theorem not_model6_eq40 : Not (Equation40 (Fin 3)) := by decideFin!
private theorem not_model6_eq41 : Not (Equation41 (Fin 3)) := by decideFin!
private theorem model6_eq43 : Equation43 (Fin 3) := by decideFin!
private theorem not_model6_eq47 : Not (Equation47 (Fin 3)) := by decideFin!
private theorem not_model6_eq56 : Not (Equation56 (Fin 3)) := by decideFin!
private theorem not_model6_eq66 : Not (Equation66 (Fin 3)) := by decideFin!
private theorem not_model6_eq75 : Not (Equation75 (Fin 3)) := by decideFin!
private theorem not_model6_eq307 : Not (Equation307 (Fin 3)) := by decideFin!
private theorem not_model6_eq308 : Not (Equation308 (Fin 3)) := by decideFin!
private theorem not_model6_eq309 : Not (Equation309 (Fin 3)) := by decideFin!
private theorem not_model6_eq310 : Not (Equation310 (Fin 3)) := by decideFin!
private theorem not_model6_eq311 : Not (Equation311 (Fin 3)) := by decideFin!
private theorem not_model6_eq312 : Not (Equation312 (Fin 3)) := by decideFin!
private theorem not_model6_eq313 : Not (Equation313 (Fin 3)) := by decideFin!
private theorem not_model6_eq314 : Not (Equation314 (Fin 3)) := by decideFin!
private theorem not_model6_eq315 : Not (Equation315 (Fin 3)) := by decideFin!
private theorem not_model6_eq316 : Not (Equation316 (Fin 3)) := by decideFin!
private theorem not_model6_eq318 : Not (Equation318 (Fin 3)) := by decideFin!
private theorem not_model6_eq323 : Not (Equation323 (Fin 3)) := by decideFin!
private theorem not_model6_eq325 : Not (Equation325 (Fin 3)) := by decideFin!
private theorem not_model6_eq326 : Not (Equation326 (Fin 3)) := by decideFin!
private theorem not_model6_eq327 : Not (Equation327 (Fin 3)) := by decideFin!
private theorem not_model6_eq329 : Not (Equation329 (Fin 3)) := by decideFin!
private theorem not_model6_eq332 : Not (Equation332 (Fin 3)) := by decideFin!
private theorem not_model6_eq333 : Not (Equation333 (Fin 3)) := by decideFin!
private theorem not_model6_eq343 : Not (Equation343 (Fin 3)) := by decideFin!
private theorem not_model6_eq411 : Not (Equation411 (Fin 3)) := by decideFin!
private theorem not_model6_eq419 : Not (Equation419 (Fin 3)) := by decideFin!
private theorem not_model6_eq429 : Not (Equation429 (Fin 3)) := by decideFin!
private theorem not_model6_eq440 : Not (Equation440 (Fin 3)) := by decideFin!
private theorem not_model6_eq477 : Not (Equation477 (Fin 3)) := by decideFin!
private theorem not_model6_eq504 : Not (Equation504 (Fin 3)) := by decideFin!
private theorem not_model6_eq513 : Not (Equation513 (Fin 3)) := by decideFin!
private theorem not_model6_eq3253 : Not (Equation3253 (Fin 3)) := by decideFin!
private theorem not_model6_eq3255 : Not (Equation3255 (Fin 3)) := by decideFin!
private theorem not_model6_eq3256 : Not (Equation3256 (Fin 3)) := by decideFin!
private theorem not_model6_eq3258 : Not (Equation3258 (Fin 3)) := by decideFin!
private theorem not_model6_eq3259 : Not (Equation3259 (Fin 3)) := by decideFin!
private theorem not_model6_eq3260 : Not (Equation3260 (Fin 3)) := by decideFin!
private theorem not_model6_eq3261 : Not (Equation3261 (Fin 3)) := by decideFin!
private theorem not_model6_eq3264 : Not (Equation3264 (Fin 3)) := by decideFin!
private theorem not_model6_eq3265 : Not (Equation3265 (Fin 3)) := by decideFin!
private theorem not_model6_eq3267 : Not (Equation3267 (Fin 3)) := by decideFin!
private theorem not_model6_eq3271 : Not (Equation3271 (Fin 3)) := by decideFin!
private theorem not_model6_eq3273 : Not (Equation3273 (Fin 3)) := by decideFin!
private theorem not_model6_eq3274 : Not (Equation3274 (Fin 3)) := by decideFin!
private theorem not_model6_eq3275 : Not (Equation3275 (Fin 3)) := by decideFin!
private theorem not_model6_eq3277 : Not (Equation3277 (Fin 3)) := by decideFin!
private theorem not_model6_eq3278 : Not (Equation3278 (Fin 3)) := by decideFin!
private theorem not_model6_eq3290 : Not (Equation3290 (Fin 3)) := by decideFin!
private theorem not_model6_eq3292 : Not (Equation3292 (Fin 3)) := by decideFin!
private theorem not_model6_eq3300 : Not (Equation3300 (Fin 3)) := by decideFin!
private theorem not_model6_eq3306 : Not (Equation3306 (Fin 3)) := by decideFin!
private theorem not_model6_eq3308 : Not (Equation3308 (Fin 3)) := by decideFin!
private theorem not_model6_eq3309 : Not (Equation3309 (Fin 3)) := by decideFin!
private theorem not_model6_eq3315 : Not (Equation3315 (Fin 3)) := by decideFin!
private theorem not_model6_eq3316 : Not (Equation3316 (Fin 3)) := by decideFin!
private theorem not_model6_eq3319 : Not (Equation3319 (Fin 3)) := by decideFin!
private theorem not_model6_eq3322 : Not (Equation3322 (Fin 3)) := by decideFin!
private theorem not_model6_eq3323 : Not (Equation3323 (Fin 3)) := by decideFin!
private theorem not_model6_eq3326 : Not (Equation3326 (Fin 3)) := by decideFin!
private theorem not_model6_eq3331 : Not (Equation3331 (Fin 3)) := by decideFin!
private theorem not_model6_eq3334 : Not (Equation3334 (Fin 3)) := by decideFin!
private theorem not_model6_eq3342 : Not (Equation3342 (Fin 3)) := by decideFin!
private theorem not_model6_eq3346 : Not (Equation3346 (Fin 3)) := by decideFin!
private theorem not_model6_eq3350 : Not (Equation3350 (Fin 3)) := by decideFin!
private theorem not_model6_eq3353 : Not (Equation3353 (Fin 3)) := by decideFin!
private theorem not_model6_eq3388 : Not (Equation3388 (Fin 3)) := by decideFin!
private theorem not_model6_eq3414 : Not (Equation3414 (Fin 3)) := by decideFin!
private theorem model6_eq4268 : Equation4268 (Fin 3) := by decideFin!
private theorem model6_eq4269 : Equation4269 (Fin 3) := by decideFin!
private theorem model6_eq4270 : Equation4270 (Fin 3) := by decideFin!
private theorem model6_eq4271 : Equation4271 (Fin 3) := by decideFin!
private theorem model6_eq4272 : Equation4272 (Fin 3) := by decideFin!
private theorem model6_eq4273 : Equation4273 (Fin 3) := by decideFin!
private theorem model6_eq4274 : Equation4274 (Fin 3) := by decideFin!
private theorem model6_eq4275 : Equation4275 (Fin 3) := by decideFin!
private theorem model6_eq4276 : Equation4276 (Fin 3) := by decideFin!
private theorem model6_eq4277 : Equation4277 (Fin 3) := by decideFin!
private theorem model6_eq4278 : Equation4278 (Fin 3) := by decideFin!
private theorem model6_eq4279 : Equation4279 (Fin 3) := by decideFin!
private theorem model6_eq4280 : Equation4280 (Fin 3) := by decideFin!
private theorem model6_eq4283 : Equation4283 (Fin 3) := by decideFin!
private theorem model6_eq4284 : Equation4284 (Fin 3) := by decideFin!
private theorem model6_eq4286 : Equation4286 (Fin 3) := by decideFin!
private theorem model6_eq4287 : Equation4287 (Fin 3) := by decideFin!
private theorem model6_eq4288 : Equation4288 (Fin 3) := by decideFin!
private theorem model6_eq4290 : Equation4290 (Fin 3) := by decideFin!
private theorem model6_eq4291 : Equation4291 (Fin 3) := by decideFin!
private theorem model6_eq4293 : Equation4293 (Fin 3) := by decideFin!
private theorem model6_eq4296 : Equation4296 (Fin 3) := by decideFin!
private theorem model6_eq4297 : Equation4297 (Fin 3) := by decideFin!
private theorem model6_eq4299 : Equation4299 (Fin 3) := by decideFin!
private theorem model6_eq4300 : Equation4300 (Fin 3) := by decideFin!
private theorem model6_eq4301 : Equation4301 (Fin 3) := by decideFin!
private theorem model6_eq4304 : Equation4304 (Fin 3) := by decideFin!
private theorem model6_eq4305 : Equation4305 (Fin 3) := by decideFin!
private theorem model6_eq4314 : Equation4314 (Fin 3) := by decideFin!
private theorem model6_eq4315 : Equation4315 (Fin 3) := by decideFin!
private theorem model6_eq4318 : Equation4318 (Fin 3) := by decideFin!
private theorem model6_eq4320 : Equation4320 (Fin 3) := by decideFin!
private theorem model6_eq4321 : Equation4321 (Fin 3) := by decideFin!
private theorem model6_eq4325 : Equation4325 (Fin 3) := by decideFin!
private theorem model6_eq4327 : Equation4327 (Fin 3) := by decideFin!
private theorem model6_eq4331 : Equation4331 (Fin 3) := by decideFin!
private theorem model6_eq4343 : Equation4343 (Fin 3) := by decideFin!
private theorem model6_eq4358 : Equation4358 (Fin 3) := by decideFin!
private theorem model6_eq4362 : Equation4362 (Fin 3) := by decideFin!
private theorem model6_eq4364 : Equation4364 (Fin 3) := by decideFin!
private theorem model6_eq4369 : Equation4369 (Fin 3) := by decideFin!
private theorem model6_eq4512 : Equation4512 (Fin 3) := by decideFin!

theorem model6_at1 : AssociativeTheory1 (Fin 3) :=
  model6_eq4512

theorem not_model6_at2 : Not (AssociativeTheory2 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq2

theorem not_model6_at3 : Not (AssociativeTheory3 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3

theorem not_model6_at4 : Not (AssociativeTheory4 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq4

theorem not_model6_at5 : Not (AssociativeTheory5 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq5

theorem not_model6_at6 : Not (AssociativeTheory6 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at7 : Not (AssociativeTheory7 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq10

theorem not_model6_at8 : Not (AssociativeTheory8 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq11

theorem not_model6_at9 : Not (AssociativeTheory9 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq14

theorem not_model6_at10 : Not (AssociativeTheory10 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq16

theorem not_model6_at11 : Not (AssociativeTheory11 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq38

theorem not_model6_at12 : Not (AssociativeTheory12 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq39

theorem not_model6_at13 : Not (AssociativeTheory13 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq38

theorem not_model6_at14 : Not (AssociativeTheory14 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem model6_at15 : AssociativeTheory15 (Fin 3) :=
  ⟨model6_eq43, model6_eq4512⟩

theorem not_model6_at16 : Not (AssociativeTheory16 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3

theorem not_model6_at17 : Not (AssociativeTheory17 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at18 : Not (AssociativeTheory18 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at19 : Not (AssociativeTheory19 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq47

theorem not_model6_at20 : Not (AssociativeTheory20 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq47

theorem not_model6_at21 : Not (AssociativeTheory21 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq56

theorem not_model6_at22 : Not (AssociativeTheory22 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq56

theorem not_model6_at23 : Not (AssociativeTheory23 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq75

theorem not_model6_at24 : Not (AssociativeTheory24 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq56

theorem not_model6_at25 : Not (AssociativeTheory25 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at26 : Not (AssociativeTheory26 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at27 : Not (AssociativeTheory27 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at28 : Not (AssociativeTheory28 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at29 : Not (AssociativeTheory29 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq308

theorem not_model6_at30 : Not (AssociativeTheory30 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at31 : Not (AssociativeTheory31 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at32 : Not (AssociativeTheory32 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq308

theorem not_model6_at33 : Not (AssociativeTheory33 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq310

theorem not_model6_at34 : Not (AssociativeTheory34 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq311

theorem not_model6_at35 : Not (AssociativeTheory35 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at36 : Not (AssociativeTheory36 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq311

theorem not_model6_at37 : Not (AssociativeTheory37 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq312

theorem not_model6_at38 : Not (AssociativeTheory38 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at39 : Not (AssociativeTheory39 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq315

theorem not_model6_at40 : Not (AssociativeTheory40 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq318

theorem not_model6_at41 : Not (AssociativeTheory41 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at42 : Not (AssociativeTheory42 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at43 : Not (AssociativeTheory43 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at44 : Not (AssociativeTheory44 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq312

theorem not_model6_at45 : Not (AssociativeTheory45 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq325

theorem not_model6_at46 : Not (AssociativeTheory46 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3

theorem not_model6_at47 : Not (AssociativeTheory47 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq308

theorem not_model6_at48 : Not (AssociativeTheory48 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at49 : Not (AssociativeTheory49 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at50 : Not (AssociativeTheory50 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at51 : Not (AssociativeTheory51 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq333

theorem not_model6_at52 : Not (AssociativeTheory52 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3

theorem not_model6_at53 : Not (AssociativeTheory53 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at54 : Not (AssociativeTheory54 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at55 : Not (AssociativeTheory55 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at56 : Not (AssociativeTheory56 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq419

theorem not_model6_at57 : Not (AssociativeTheory57 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq429

theorem not_model6_at58 : Not (AssociativeTheory58 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq440

theorem not_model6_at59 : Not (AssociativeTheory59 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq440

theorem not_model6_at60 : Not (AssociativeTheory60 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq504

theorem not_model6_at61 : Not (AssociativeTheory61 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq513

theorem not_model6_at62 : Not (AssociativeTheory62 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq440

theorem not_model6_at63 : Not (AssociativeTheory63 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at64 : Not (AssociativeTheory64 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at65 : Not (AssociativeTheory65 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3255

theorem not_model6_at66 : Not (AssociativeTheory66 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at67 : Not (AssociativeTheory67 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3256

theorem not_model6_at68 : Not (AssociativeTheory68 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3258

theorem not_model6_at69 : Not (AssociativeTheory69 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at70 : Not (AssociativeTheory70 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3255

theorem not_model6_at71 : Not (AssociativeTheory71 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3259

theorem not_model6_at72 : Not (AssociativeTheory72 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3260

theorem not_model6_at73 : Not (AssociativeTheory73 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at74 : Not (AssociativeTheory74 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3261

theorem not_model6_at75 : Not (AssociativeTheory75 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3264

theorem not_model6_at76 : Not (AssociativeTheory76 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at77 : Not (AssociativeTheory77 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq308

theorem not_model6_at78 : Not (AssociativeTheory78 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq312

theorem not_model6_at79 : Not (AssociativeTheory79 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3260

theorem not_model6_at80 : Not (AssociativeTheory80 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at81 : Not (AssociativeTheory81 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3265

theorem not_model6_at82 : Not (AssociativeTheory82 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at83 : Not (AssociativeTheory83 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3260

theorem not_model6_at84 : Not (AssociativeTheory84 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at85 : Not (AssociativeTheory85 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3264

theorem not_model6_at86 : Not (AssociativeTheory86 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at87 : Not (AssociativeTheory87 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3260

theorem not_model6_at88 : Not (AssociativeTheory88 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at89 : Not (AssociativeTheory89 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem not_model6_at90 : Not (AssociativeTheory90 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at91 : Not (AssociativeTheory91 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem not_model6_at92 : Not (AssociativeTheory92 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at93 : Not (AssociativeTheory93 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at94 : Not (AssociativeTheory94 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3271

theorem not_model6_at95 : Not (AssociativeTheory95 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3274

theorem not_model6_at96 : Not (AssociativeTheory96 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3264

theorem not_model6_at97 : Not (AssociativeTheory97 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3278

theorem not_model6_at98 : Not (AssociativeTheory98 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3292

theorem not_model6_at99 : Not (AssociativeTheory99 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3264

theorem not_model6_at100 : Not (AssociativeTheory100 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3274

theorem not_model6_at101 : Not (AssociativeTheory101 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3264

theorem not_model6_at102 : Not (AssociativeTheory102 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3300

theorem not_model6_at103 : Not (AssociativeTheory103 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at104 : Not (AssociativeTheory104 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem not_model6_at105 : Not (AssociativeTheory105 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at106 : Not (AssociativeTheory106 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem not_model6_at107 : Not (AssociativeTheory107 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3256

theorem not_model6_at108 : Not (AssociativeTheory108 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3261

theorem not_model6_at109 : Not (AssociativeTheory109 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3271

theorem not_model6_at110 : Not (AssociativeTheory110 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3278

theorem not_model6_at111 : Not (AssociativeTheory111 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3308

theorem not_model6_at112 : Not (AssociativeTheory112 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at113 : Not (AssociativeTheory113 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3315

theorem not_model6_at114 : Not (AssociativeTheory114 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at115 : Not (AssociativeTheory115 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3256

theorem not_model6_at116 : Not (AssociativeTheory116 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem not_model6_at117 : Not (AssociativeTheory117 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3316

theorem not_model6_at118 : Not (AssociativeTheory118 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at119 : Not (AssociativeTheory119 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at120 : Not (AssociativeTheory120 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3319

theorem not_model6_at121 : Not (AssociativeTheory121 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem not_model6_at122 : Not (AssociativeTheory122 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3346

theorem not_model6_at123 : Not (AssociativeTheory123 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at124 : Not (AssociativeTheory124 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3353

theorem not_model6_at125 : Not (AssociativeTheory125 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at126 : Not (AssociativeTheory126 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3319

theorem model6_at127 : AssociativeTheory127 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4512⟩

theorem model6_at128 : AssociativeTheory128 (Fin 3) :=
  ⟨model6_eq43, model6_eq4268, model6_eq4512⟩

theorem model6_at129 : AssociativeTheory129 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4512⟩

theorem model6_at130 : AssociativeTheory130 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4269, model6_eq4512⟩

theorem model6_at131 : AssociativeTheory131 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4512⟩

theorem model6_at132 : AssociativeTheory132 (Fin 3) :=
  ⟨model6_eq43, model6_eq4270, model6_eq4512⟩

theorem model6_at133 : AssociativeTheory133 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4270, model6_eq4512⟩

theorem model6_at134 : AssociativeTheory134 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4270, model6_eq4512⟩

theorem model6_at135 : AssociativeTheory135 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4269, model6_eq4270, model6_eq4512⟩

theorem model6_at136 : AssociativeTheory136 (Fin 3) :=
  ⟨model6_eq4271, model6_eq4512⟩

theorem model6_at137 : AssociativeTheory137 (Fin 3) :=
  ⟨model6_eq43, model6_eq4271, model6_eq4512⟩

theorem model6_at138 : AssociativeTheory138 (Fin 3) :=
  ⟨model6_eq4272, model6_eq4512⟩

theorem model6_at139 : AssociativeTheory139 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4272, model6_eq4512⟩

theorem model6_at140 : AssociativeTheory140 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4272, model6_eq4512⟩

theorem model6_at141 : AssociativeTheory141 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4269, model6_eq4272, model6_eq4512⟩

theorem model6_at142 : AssociativeTheory142 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4272, model6_eq4512⟩

theorem model6_at143 : AssociativeTheory143 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4270, model6_eq4272, model6_eq4512⟩

theorem model6_at144 : AssociativeTheory144 (Fin 3) :=
  ⟨model6_eq4271, model6_eq4272, model6_eq4512⟩

theorem model6_at145 : AssociativeTheory145 (Fin 3) :=
  ⟨model6_eq4273, model6_eq4512⟩

theorem not_model6_at146 : Not (AssociativeTheory146 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem model6_at147 : AssociativeTheory147 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4273, model6_eq4512⟩

theorem model6_at148 : AssociativeTheory148 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4273, model6_eq4512⟩

theorem model6_at149 : AssociativeTheory149 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4273, model6_eq4512⟩

theorem model6_at150 : AssociativeTheory150 (Fin 3) :=
  ⟨model6_eq4275, model6_eq4512⟩

theorem model6_at151 : AssociativeTheory151 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4275, model6_eq4512⟩

theorem model6_at152 : AssociativeTheory152 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4275, model6_eq4512⟩

theorem model6_at153 : AssociativeTheory153 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4275, model6_eq4512⟩

theorem model6_at154 : AssociativeTheory154 (Fin 3) :=
  ⟨model6_eq4272, model6_eq4275, model6_eq4512⟩

theorem model6_at155 : AssociativeTheory155 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4272, model6_eq4275, model6_eq4512⟩

theorem model6_at156 : AssociativeTheory156 (Fin 3) :=
  ⟨model6_eq4273, model6_eq4275, model6_eq4512⟩

theorem model6_at157 : AssociativeTheory157 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4273, model6_eq4275, model6_eq4512⟩

theorem model6_at158 : AssociativeTheory158 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4512⟩

theorem model6_at159 : AssociativeTheory159 (Fin 3) :=
  ⟨model6_eq43, model6_eq4276, model6_eq4512⟩

theorem model6_at160 : AssociativeTheory160 (Fin 3) :=
  ⟨model6_eq4278, model6_eq4512⟩

theorem model6_at161 : AssociativeTheory161 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4512⟩

theorem not_model6_at162 : Not (AssociativeTheory162 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq47

theorem not_model6_at163 : Not (AssociativeTheory163 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq56

theorem not_model6_at164 : Not (AssociativeTheory164 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at165 : Not (AssociativeTheory165 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at166 : Not (AssociativeTheory166 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at167 : Not (AssociativeTheory167 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq440

theorem not_model6_at168 : Not (AssociativeTheory168 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at169 : Not (AssociativeTheory169 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3256

theorem not_model6_at170 : Not (AssociativeTheory170 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3319

theorem model6_at171 : AssociativeTheory171 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4283, model6_eq4512⟩

theorem model6_at172 : AssociativeTheory172 (Fin 3) :=
  ⟨model6_eq4272, model6_eq4283, model6_eq4512⟩

theorem model6_at173 : AssociativeTheory173 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4512⟩

theorem model6_at174 : AssociativeTheory174 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4512⟩

theorem model6_at175 : AssociativeTheory175 (Fin 3) :=
  ⟨model6_eq43, model6_eq4284, model6_eq4512⟩

theorem not_model6_at176 : Not (AssociativeTheory176 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at177 : Not (AssociativeTheory177 (Fin 3)) := by
  refine not_and_of_not_right _ ?_
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at178 : AssociativeTheory178 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4284, model6_eq4512⟩

theorem model6_at179 : AssociativeTheory179 (Fin 3) :=
  ⟨model6_eq4273, model6_eq4284, model6_eq4512⟩

theorem model6_at180 : AssociativeTheory180 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4512⟩

theorem model6_at181 : AssociativeTheory181 (Fin 3) :=
  ⟨model6_eq43, model6_eq4276, model6_eq4284, model6_eq4512⟩

theorem model6_at182 : AssociativeTheory182 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4284, model6_eq4512⟩

theorem not_model6_at183 : Not (AssociativeTheory183 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at184 : AssociativeTheory184 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4284, model6_eq4512⟩

theorem model6_at185 : AssociativeTheory185 (Fin 3) :=
  ⟨model6_eq4287, model6_eq4512⟩

theorem not_model6_at186 : Not (AssociativeTheory186 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at187 : AssociativeTheory187 (Fin 3) :=
  ⟨model6_eq4290, model6_eq4512⟩

theorem not_model6_at188 : Not (AssociativeTheory188 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at189 : Not (AssociativeTheory189 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at190 : Not (AssociativeTheory190 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem model6_at191 : AssociativeTheory191 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4290, model6_eq4512⟩

theorem model6_at192 : AssociativeTheory192 (Fin 3) :=
  ⟨model6_eq4273, model6_eq4290, model6_eq4512⟩

theorem model6_at193 : AssociativeTheory193 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4290, model6_eq4512⟩

theorem model6_at194 : AssociativeTheory194 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4290, model6_eq4512⟩

theorem not_model6_at195 : Not (AssociativeTheory195 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at196 : Not (AssociativeTheory196 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem model6_at197 : AssociativeTheory197 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4290, model6_eq4512⟩

theorem model6_at198 : AssociativeTheory198 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4290, model6_eq4512⟩

theorem not_model6_at199 : Not (AssociativeTheory199 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at200 : AssociativeTheory200 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4284, model6_eq4290, model6_eq4512⟩

theorem model6_at201 : AssociativeTheory201 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4290, model6_eq4512⟩

theorem model6_at202 : AssociativeTheory202 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4284, model6_eq4290, model6_eq4512⟩

theorem not_model6_at203 : Not (AssociativeTheory203 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at204 : AssociativeTheory204 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4284, model6_eq4290, model6_eq4512⟩

theorem model6_at205 : AssociativeTheory205 (Fin 3) :=
  ⟨model6_eq4291, model6_eq4512⟩

theorem not_model6_at206 : Not (AssociativeTheory206 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at207 : Not (AssociativeTheory207 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq312

theorem not_model6_at208 : Not (AssociativeTheory208 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem model6_at209 : AssociativeTheory209 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4291, model6_eq4512⟩

theorem model6_at210 : AssociativeTheory210 (Fin 3) :=
  ⟨model6_eq4272, model6_eq4291, model6_eq4512⟩

theorem model6_at211 : AssociativeTheory211 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4291, model6_eq4512⟩

theorem model6_at212 : AssociativeTheory212 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4291, model6_eq4512⟩

theorem not_model6_at213 : Not (AssociativeTheory213 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at214 : Not (AssociativeTheory214 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem model6_at215 : AssociativeTheory215 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4283, model6_eq4291, model6_eq4512⟩

theorem model6_at216 : AssociativeTheory216 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4291, model6_eq4512⟩

theorem model6_at217 : AssociativeTheory217 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4291, model6_eq4512⟩

theorem not_model6_at218 : Not (AssociativeTheory218 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at219 : AssociativeTheory219 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4291, model6_eq4512⟩

theorem model6_at220 : AssociativeTheory220 (Fin 3) :=
  ⟨model6_eq4290, model6_eq4291, model6_eq4512⟩

theorem model6_at221 : AssociativeTheory221 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4290, model6_eq4291, model6_eq4512⟩

theorem model6_at222 : AssociativeTheory222 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4512⟩

theorem not_model6_at223 : Not (AssociativeTheory223 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at224 : AssociativeTheory224 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4293, model6_eq4512⟩

theorem model6_at225 : AssociativeTheory225 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4293, model6_eq4512⟩

theorem model6_at226 : AssociativeTheory226 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4270, model6_eq4293, model6_eq4512⟩

theorem model6_at227 : AssociativeTheory227 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4512⟩

theorem model6_at228 : AssociativeTheory228 (Fin 3) :=
  ⟨model6_eq4300, model6_eq4512⟩

theorem not_model6_at229 : Not (AssociativeTheory229 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at230 : AssociativeTheory230 (Fin 3) :=
  ⟨model6_eq4314, model6_eq4512⟩

theorem not_model6_at231 : Not (AssociativeTheory231 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at232 : Not (AssociativeTheory232 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq308

theorem not_model6_at233 : Not (AssociativeTheory233 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem model6_at234 : AssociativeTheory234 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4314, model6_eq4512⟩

theorem model6_at235 : AssociativeTheory235 (Fin 3) :=
  ⟨model6_eq4275, model6_eq4314, model6_eq4512⟩

theorem model6_at236 : AssociativeTheory236 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4314, model6_eq4512⟩

theorem model6_at237 : AssociativeTheory237 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4314, model6_eq4512⟩

theorem model6_at238 : AssociativeTheory238 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4314, model6_eq4512⟩

theorem model6_at239 : AssociativeTheory239 (Fin 3) :=
  ⟨model6_eq4315, model6_eq4512⟩

theorem not_model6_at240 : Not (AssociativeTheory240 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at241 : AssociativeTheory241 (Fin 3) :=
  ⟨model6_eq4320, model6_eq4512⟩

theorem not_model6_at242 : Not (AssociativeTheory242 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq47

theorem not_model6_at243 : Not (AssociativeTheory243 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq75

theorem not_model6_at244 : Not (AssociativeTheory244 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at245 : Not (AssociativeTheory245 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at246 : Not (AssociativeTheory246 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at247 : Not (AssociativeTheory247 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq513

theorem not_model6_at248 : Not (AssociativeTheory248 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at249 : Not (AssociativeTheory249 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3261

theorem not_model6_at250 : Not (AssociativeTheory250 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem model6_at251 : AssociativeTheory251 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4320, model6_eq4512⟩

theorem model6_at252 : AssociativeTheory252 (Fin 3) :=
  ⟨model6_eq4275, model6_eq4320, model6_eq4512⟩

theorem model6_at253 : AssociativeTheory253 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4320, model6_eq4512⟩

theorem model6_at254 : AssociativeTheory254 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4320, model6_eq4512⟩

theorem model6_at255 : AssociativeTheory255 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4320, model6_eq4512⟩

theorem model6_at256 : AssociativeTheory256 (Fin 3) :=
  ⟨model6_eq4314, model6_eq4320, model6_eq4512⟩

theorem not_model6_at257 : Not (AssociativeTheory257 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at258 : Not (AssociativeTheory258 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem model6_at259 : AssociativeTheory259 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4314, model6_eq4320, model6_eq4512⟩

theorem model6_at260 : AssociativeTheory260 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4314, model6_eq4320, model6_eq4512⟩

theorem model6_at261 : AssociativeTheory261 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4314, model6_eq4320, model6_eq4512⟩

theorem model6_at262 : AssociativeTheory262 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4314, model6_eq4320, model6_eq4512⟩

theorem model6_at263 : AssociativeTheory263 (Fin 3) :=
  ⟨model6_eq4321, model6_eq4512⟩

theorem not_model6_at264 : Not (AssociativeTheory264 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at265 : Not (AssociativeTheory265 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at266 : Not (AssociativeTheory266 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3260

theorem not_model6_at267 : Not (AssociativeTheory267 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3265

theorem not_model6_at268 : Not (AssociativeTheory268 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3260

theorem not_model6_at269 : Not (AssociativeTheory269 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem model6_at270 : AssociativeTheory270 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4321, model6_eq4512⟩

theorem model6_at271 : AssociativeTheory271 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4321, model6_eq4512⟩

theorem model6_at272 : AssociativeTheory272 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4270, model6_eq4321, model6_eq4512⟩

theorem model6_at273 : AssociativeTheory273 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4321, model6_eq4512⟩

theorem model6_at274 : AssociativeTheory274 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4321, model6_eq4512⟩

theorem not_model6_at275 : Not (AssociativeTheory275 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at276 : AssociativeTheory276 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4321, model6_eq4512⟩

theorem model6_at277 : AssociativeTheory277 (Fin 3) :=
  ⟨model6_eq4290, model6_eq4321, model6_eq4512⟩

theorem model6_at278 : AssociativeTheory278 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4290, model6_eq4321, model6_eq4512⟩

theorem model6_at279 : AssociativeTheory279 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4290, model6_eq4321, model6_eq4512⟩

theorem model6_at280 : AssociativeTheory280 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4290, model6_eq4321, model6_eq4512⟩

theorem model6_at281 : AssociativeTheory281 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4321, model6_eq4512⟩

theorem not_model6_at282 : Not (AssociativeTheory282 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at283 : AssociativeTheory283 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4293, model6_eq4321, model6_eq4512⟩

theorem model6_at284 : AssociativeTheory284 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4321, model6_eq4512⟩

theorem model6_at285 : AssociativeTheory285 (Fin 3) :=
  ⟨model6_eq4343, model6_eq4512⟩

theorem not_model6_at286 : Not (AssociativeTheory286 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at287 : AssociativeTheory287 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4343, model6_eq4512⟩

theorem model6_at288 : AssociativeTheory288 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4343, model6_eq4512⟩

theorem model6_at289 : AssociativeTheory289 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4269, model6_eq4343, model6_eq4512⟩

theorem model6_at290 : AssociativeTheory290 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4343, model6_eq4512⟩

theorem model6_at291 : AssociativeTheory291 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4343, model6_eq4512⟩

theorem model6_at292 : AssociativeTheory292 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4343, model6_eq4512⟩

theorem model6_at293 : AssociativeTheory293 (Fin 3) :=
  ⟨model6_eq4291, model6_eq4343, model6_eq4512⟩

theorem model6_at294 : AssociativeTheory294 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4291, model6_eq4343, model6_eq4512⟩

theorem model6_at295 : AssociativeTheory295 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4291, model6_eq4343, model6_eq4512⟩

theorem model6_at296 : AssociativeTheory296 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4291, model6_eq4343, model6_eq4512⟩

theorem model6_at297 : AssociativeTheory297 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4343, model6_eq4512⟩

theorem model6_at298 : AssociativeTheory298 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4293, model6_eq4343, model6_eq4512⟩

theorem model6_at299 : AssociativeTheory299 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4343, model6_eq4512⟩

theorem model6_at300 : AssociativeTheory300 (Fin 3) :=
  ⟨model6_eq4321, model6_eq4343, model6_eq4512⟩

theorem not_model6_at301 : Not (AssociativeTheory301 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at302 : AssociativeTheory302 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4321, model6_eq4343, model6_eq4512⟩

theorem model6_at303 : AssociativeTheory303 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4321, model6_eq4343, model6_eq4512⟩

theorem model6_at304 : AssociativeTheory304 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4321, model6_eq4343, model6_eq4512⟩

theorem model6_at305 : AssociativeTheory305 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4321, model6_eq4343, model6_eq4512⟩

theorem model6_at306 : AssociativeTheory306 (Fin 3) :=
  ⟨model6_eq4358, model6_eq4512⟩

theorem not_model6_at307 : Not (AssociativeTheory307 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3

theorem not_model6_at308 : Not (AssociativeTheory308 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at309 : Not (AssociativeTheory309 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at310 : Not (AssociativeTheory310 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq47

theorem not_model6_at311 : Not (AssociativeTheory311 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at312 : Not (AssociativeTheory312 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at313 : Not (AssociativeTheory313 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq308

theorem not_model6_at314 : Not (AssociativeTheory314 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at315 : Not (AssociativeTheory315 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at316 : Not (AssociativeTheory316 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at317 : Not (AssociativeTheory317 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at318 : Not (AssociativeTheory318 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3256

theorem not_model6_at319 : Not (AssociativeTheory319 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem not_model6_at320 : Not (AssociativeTheory320 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at321 : Not (AssociativeTheory321 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem not_model6_at322 : Not (AssociativeTheory322 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3319

theorem model6_at323 : AssociativeTheory323 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4358, model6_eq4512⟩

theorem model6_at324 : AssociativeTheory324 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4358, model6_eq4512⟩

theorem model6_at325 : AssociativeTheory325 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4270, model6_eq4358, model6_eq4512⟩

theorem model6_at326 : AssociativeTheory326 (Fin 3) :=
  ⟨model6_eq4272, model6_eq4358, model6_eq4512⟩

theorem model6_at327 : AssociativeTheory327 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4272, model6_eq4358, model6_eq4512⟩

theorem model6_at328 : AssociativeTheory328 (Fin 3) :=
  ⟨model6_eq4273, model6_eq4358, model6_eq4512⟩

theorem model6_at329 : AssociativeTheory329 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4273, model6_eq4358, model6_eq4512⟩

theorem model6_at330 : AssociativeTheory330 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4273, model6_eq4358, model6_eq4512⟩

theorem model6_at331 : AssociativeTheory331 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4358, model6_eq4512⟩

theorem model6_at332 : AssociativeTheory332 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4358, model6_eq4512⟩

theorem not_model6_at333 : Not (AssociativeTheory333 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at334 : AssociativeTheory334 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4358, model6_eq4512⟩

theorem model6_at335 : AssociativeTheory335 (Fin 3) :=
  ⟨model6_eq4290, model6_eq4358, model6_eq4512⟩

theorem not_model6_at336 : Not (AssociativeTheory336 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at337 : Not (AssociativeTheory337 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem model6_at338 : AssociativeTheory338 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4290, model6_eq4358, model6_eq4512⟩

theorem model6_at339 : AssociativeTheory339 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4290, model6_eq4358, model6_eq4512⟩

theorem not_model6_at340 : Not (AssociativeTheory340 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at341 : AssociativeTheory341 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4290, model6_eq4358, model6_eq4512⟩

theorem model6_at342 : AssociativeTheory342 (Fin 3) :=
  ⟨model6_eq4291, model6_eq4358, model6_eq4512⟩

theorem not_model6_at343 : Not (AssociativeTheory343 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at344 : AssociativeTheory344 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4291, model6_eq4358, model6_eq4512⟩

theorem model6_at345 : AssociativeTheory345 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4291, model6_eq4358, model6_eq4512⟩

theorem model6_at346 : AssociativeTheory346 (Fin 3) :=
  ⟨model6_eq4343, model6_eq4358, model6_eq4512⟩

theorem model6_at347 : AssociativeTheory347 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4343, model6_eq4358, model6_eq4512⟩

theorem model6_at348 : AssociativeTheory348 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4343, model6_eq4358, model6_eq4512⟩

theorem model6_at349 : AssociativeTheory349 (Fin 3) :=
  ⟨model6_eq4291, model6_eq4343, model6_eq4358, model6_eq4512⟩

theorem model6_at350 : AssociativeTheory350 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4291, model6_eq4343, model6_eq4358, model6_eq4512⟩

theorem model6_at351 : AssociativeTheory351 (Fin 3) :=
  ⟨model6_eq4362, model6_eq4512⟩

theorem not_model6_at352 : Not (AssociativeTheory352 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3

theorem not_model6_at353 : Not (AssociativeTheory353 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq8

theorem not_model6_at354 : Not (AssociativeTheory354 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at355 : Not (AssociativeTheory355 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq47

theorem not_model6_at356 : Not (AssociativeTheory356 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at357 : Not (AssociativeTheory357 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at358 : Not (AssociativeTheory358 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at359 : Not (AssociativeTheory359 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq323

theorem not_model6_at360 : Not (AssociativeTheory360 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq326

theorem not_model6_at361 : Not (AssociativeTheory361 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq411

theorem not_model6_at362 : Not (AssociativeTheory362 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at363 : Not (AssociativeTheory363 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3261

theorem not_model6_at364 : Not (AssociativeTheory364 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem not_model6_at365 : Not (AssociativeTheory365 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3300

theorem not_model6_at366 : Not (AssociativeTheory366 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3306

theorem not_model6_at367 : Not (AssociativeTheory367 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3319

theorem model6_at368 : AssociativeTheory368 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4362, model6_eq4512⟩

theorem model6_at369 : AssociativeTheory369 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4362, model6_eq4512⟩

theorem model6_at370 : AssociativeTheory370 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4269, model6_eq4362, model6_eq4512⟩

theorem model6_at371 : AssociativeTheory371 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4362, model6_eq4512⟩

theorem model6_at372 : AssociativeTheory372 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4270, model6_eq4362, model6_eq4512⟩

theorem model6_at373 : AssociativeTheory373 (Fin 3) :=
  ⟨model6_eq4275, model6_eq4362, model6_eq4512⟩

theorem model6_at374 : AssociativeTheory374 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4275, model6_eq4362, model6_eq4512⟩

theorem model6_at375 : AssociativeTheory375 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4275, model6_eq4362, model6_eq4512⟩

theorem model6_at376 : AssociativeTheory376 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4362, model6_eq4512⟩

theorem model6_at377 : AssociativeTheory377 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4362, model6_eq4512⟩

theorem not_model6_at378 : Not (AssociativeTheory378 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at379 : Not (AssociativeTheory379 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem model6_at380 : AssociativeTheory380 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4362, model6_eq4512⟩

theorem model6_at381 : AssociativeTheory381 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4362, model6_eq4512⟩

theorem not_model6_at382 : Not (AssociativeTheory382 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at383 : AssociativeTheory383 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4362, model6_eq4512⟩

theorem model6_at384 : AssociativeTheory384 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4284, model6_eq4362, model6_eq4512⟩

theorem not_model6_at385 : Not (AssociativeTheory385 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at386 : AssociativeTheory386 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4284, model6_eq4362, model6_eq4512⟩

theorem model6_at387 : AssociativeTheory387 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4362, model6_eq4512⟩

theorem model6_at388 : AssociativeTheory388 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4293, model6_eq4362, model6_eq4512⟩

theorem model6_at389 : AssociativeTheory389 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4362, model6_eq4512⟩

theorem model6_at390 : AssociativeTheory390 (Fin 3) :=
  ⟨model6_eq4314, model6_eq4362, model6_eq4512⟩

theorem not_model6_at391 : Not (AssociativeTheory391 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at392 : AssociativeTheory392 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4314, model6_eq4362, model6_eq4512⟩

theorem model6_at393 : AssociativeTheory393 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4314, model6_eq4362, model6_eq4512⟩

theorem model6_at394 : AssociativeTheory394 (Fin 3) :=
  ⟨model6_eq4293, model6_eq4314, model6_eq4362, model6_eq4512⟩

theorem model6_at395 : AssociativeTheory395 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4293, model6_eq4314, model6_eq4362, model6_eq4512⟩

theorem model6_at396 : AssociativeTheory396 (Fin 3) :=
  ⟨model6_eq4358, model6_eq4362, model6_eq4512⟩

theorem not_model6_at397 : Not (AssociativeTheory397 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at398 : Not (AssociativeTheory398 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at399 : Not (AssociativeTheory399 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at400 : Not (AssociativeTheory400 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at401 : Not (AssociativeTheory401 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem model6_at402 : AssociativeTheory402 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4358, model6_eq4362, model6_eq4512⟩

theorem model6_at403 : AssociativeTheory403 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4358, model6_eq4362, model6_eq4512⟩

theorem model6_at404 : AssociativeTheory404 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4358, model6_eq4362, model6_eq4512⟩

theorem model6_at405 : AssociativeTheory405 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4358, model6_eq4362, model6_eq4512⟩

theorem not_model6_at406 : Not (AssociativeTheory406 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at407 : AssociativeTheory407 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4358, model6_eq4362, model6_eq4512⟩

theorem model6_at408 : AssociativeTheory408 (Fin 3) :=
  ⟨model6_eq4364, model6_eq4512⟩

theorem not_model6_at409 : Not (AssociativeTheory409 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at410 : Not (AssociativeTheory410 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at411 : Not (AssociativeTheory411 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at412 : Not (AssociativeTheory412 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at413 : Not (AssociativeTheory413 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem model6_at414 : AssociativeTheory414 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4364, model6_eq4512⟩

theorem model6_at415 : AssociativeTheory415 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4364, model6_eq4512⟩

theorem model6_at416 : AssociativeTheory416 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4364, model6_eq4512⟩

theorem model6_at417 : AssociativeTheory417 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4364, model6_eq4512⟩

theorem not_model6_at418 : Not (AssociativeTheory418 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at419 : AssociativeTheory419 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4364, model6_eq4512⟩

theorem model6_at420 : AssociativeTheory420 (Fin 3) :=
  ⟨model6_eq4369, model6_eq4512⟩

theorem not_model6_at421 : Not (AssociativeTheory421 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at422 : Not (AssociativeTheory422 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at423 : Not (AssociativeTheory423 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at424 : Not (AssociativeTheory424 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem not_model6_at425 : Not (AssociativeTheory425 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem not_model6_at426 : Not (AssociativeTheory426 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem not_model6_at427 : Not (AssociativeTheory427 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq309

theorem model6_at428 : AssociativeTheory428 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4369, model6_eq4512⟩

theorem model6_at429 : AssociativeTheory429 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4369, model6_eq4512⟩

theorem model6_at430 : AssociativeTheory430 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4269, model6_eq4369, model6_eq4512⟩

theorem model6_at431 : AssociativeTheory431 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4369, model6_eq4512⟩

theorem model6_at432 : AssociativeTheory432 (Fin 3) :=
  ⟨model6_eq4273, model6_eq4369, model6_eq4512⟩

theorem not_model6_at433 : Not (AssociativeTheory433 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem model6_at434 : AssociativeTheory434 (Fin 3) :=
  ⟨model6_eq4270, model6_eq4273, model6_eq4369, model6_eq4512⟩

theorem model6_at435 : AssociativeTheory435 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4369, model6_eq4512⟩

theorem model6_at436 : AssociativeTheory436 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4369, model6_eq4512⟩

theorem not_model6_at437 : Not (AssociativeTheory437 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at438 : Not (AssociativeTheory438 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3253

theorem model6_at439 : AssociativeTheory439 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4369, model6_eq4512⟩

theorem model6_at440 : AssociativeTheory440 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4369, model6_eq4512⟩

theorem not_model6_at441 : Not (AssociativeTheory441 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at442 : AssociativeTheory442 (Fin 3) :=
  ⟨model6_eq4269, model6_eq4284, model6_eq4369, model6_eq4512⟩

theorem model6_at443 : AssociativeTheory443 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4369, model6_eq4512⟩

theorem model6_at444 : AssociativeTheory444 (Fin 3) :=
  ⟨model6_eq4283, model6_eq4284, model6_eq4369, model6_eq4512⟩

theorem not_model6_at445 : Not (AssociativeTheory445 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem model6_at446 : AssociativeTheory446 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4283, model6_eq4284, model6_eq4369, model6_eq4512⟩

theorem model6_at447 : AssociativeTheory447 (Fin 3) :=
  ⟨model6_eq4291, model6_eq4369, model6_eq4512⟩

theorem model6_at448 : AssociativeTheory448 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4291, model6_eq4369, model6_eq4512⟩

theorem model6_at449 : AssociativeTheory449 (Fin 3) :=
  ⟨model6_eq4321, model6_eq4369, model6_eq4512⟩

theorem not_model6_at450 : Not (AssociativeTheory450 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq40

theorem not_model6_at451 : Not (AssociativeTheory451 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq307

theorem not_model6_at452 : Not (AssociativeTheory452 (Fin 3)) := by
  refine not_and_of_not_left _ ?_
  exact not_model6_eq3267

theorem model6_at453 : AssociativeTheory453 (Fin 3) :=
  ⟨model6_eq4268, model6_eq4321, model6_eq4369, model6_eq4512⟩

theorem model6_at454 : AssociativeTheory454 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4321, model6_eq4369, model6_eq4512⟩

theorem model6_at455 : AssociativeTheory455 (Fin 3) :=
  ⟨model6_eq4284, model6_eq4321, model6_eq4369, model6_eq4512⟩

theorem model6_at456 : AssociativeTheory456 (Fin 3) :=
  ⟨model6_eq4276, model6_eq4284, model6_eq4321, model6_eq4369, model6_eq4512⟩
