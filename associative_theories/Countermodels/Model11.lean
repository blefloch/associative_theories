import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod

private def model11_op := finOpTable "[[0,1,2],[1,2,0],[2,0,1]]"

@[equational_result]
theorem facts_from_model11 :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
  [1, 43, 47, 56, 66, 75, 4276, 4283, 4290, 4320, 4358, 4362, 4364, 4369, 4512]
  [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 40, 41, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 323, 325, 326, 327, 329, 332, 333, 343, 411, 419, 429, 440, 477, 504, 513, 3253, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3271, 3273, 3274, 3275, 3277, 3278, 3290, 3292, 3300, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3346, 3350, 3353, 3388, 3414, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4277, 4278, 4279, 4280, 4284, 4286, 4287, 4288, 4291, 4293, 4296, 4297, 4299, 4300, 4301, 4304, 4305, 4314, 4315, 4318, 4321, 4325, 4327, 4331, 4343]
  :=
  ⟨_, Magma.mk model11_op, Finite.of_fintype _, by decideFin!⟩

