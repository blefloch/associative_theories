import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod

private def model4_op := finOpTable "[[0,1],[0,1]]"

@[equational_result]
theorem facts_from_model4 :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
  [1, 3, 5, 8, 10, 16, 39, 47, 75, 307, 309, 312, 315, 318, 323, 326, 329, 333, 343, 411, 419, 429, 513, 3253, 3255, 3258, 3261, 3264, 3271, 3274, 3278, 3292, 3300, 3306, 3309, 3316, 3319, 3322, 3326, 3334, 3346, 3353, 3388, 3414, 4269, 4272, 4275, 4278, 4284, 4287, 4291, 4296, 4300, 4304, 4320, 4327, 4362, 4512]
  [2, 4, 11, 14, 38, 40, 41, 43, 56, 66, 308, 310, 311, 313, 314, 316, 325, 327, 332, 440, 477, 504, 3256, 3259, 3260, 3265, 3267, 3273, 3275, 3277, 3290, 3308, 3315, 3323, 3331, 3342, 3350, 4268, 4270, 4271, 4273, 4274, 4276, 4277, 4279, 4280, 4283, 4286, 4288, 4290, 4293, 4297, 4299, 4301, 4305, 4314, 4315, 4318, 4321, 4325, 4331, 4343, 4358, 4364, 4369]
  :=
  ⟨_, Magma.mk model4_op, Finite.of_fintype _, by decideFin!⟩

