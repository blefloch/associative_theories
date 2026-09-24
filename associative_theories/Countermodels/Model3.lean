import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod

private def model3_op := finOpTable "[[0,0],[1,1]]"

theorem facts_from_model3 :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
  [1, 3, 4, 8, 10, 11, 38, 47, 56, 307, 308, 309, 310, 311, 323, 325, 326, 327, 329, 411, 419, 429, 440, 3253, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 4268, 4269, 4270, 4271, 4283, 4284, 4286, 4287, 4288, 4314, 4315, 4318, 4358, 4512]
  [2, 5, 14, 16, 39, 40, 41, 43, 66, 75, 312, 313, 314, 315, 316, 318, 332, 333, 343, 477, 504, 513, 3271, 3273, 3274, 3275, 3277, 3278, 3290, 3292, 3300, 3342, 3346, 3350, 3353, 3388, 3414, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4290, 4291, 4293, 4296, 4297, 4299, 4300, 4301, 4304, 4305, 4320, 4321, 4325, 4327, 4331, 4343, 4362, 4364, 4369]
  :=
  ⟨_, Magma.mk model3_op, Finite.of_fintype _, by decideFin!⟩

