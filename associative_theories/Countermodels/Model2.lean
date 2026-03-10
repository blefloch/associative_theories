import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod

private def model2_op := finOpTable "[[0,0],[0,1]]"

@[equational_result]
theorem facts_from_model2 :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
  [1, 3, 8, 43, 47, 307, 323, 325, 326, 332, 333, 411, 3253, 3306, 3308, 3309, 3315, 3316, 3319, 3342, 3346, 3353, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4358, 4362, 4364, 4369, 4512]
  [2, 4, 5, 10, 11, 14, 16, 38, 39, 40, 41, 56, 66, 75, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 327, 329, 343, 419, 429, 440, 477, 504, 513, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3271, 3273, 3274, 3275, 3277, 3278, 3290, 3292, 3300, 3322, 3323, 3326, 3331, 3334, 3350, 3388, 3414, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4286, 4287, 4288, 4296, 4297, 4299, 4300, 4301, 4304, 4305, 4315, 4318, 4325, 4327, 4331]
  :=
  ⟨_, Magma.mk model2_op, Finite.of_fintype _, by decideFin!⟩

