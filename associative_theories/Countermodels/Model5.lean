import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod

private def model5_op := finOpTable "[[0,1],[1,0]]"

theorem facts_from_model5 :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
  [1, 8, 11, 14, 16, 40, 43, 411, 419, 429, 440, 477, 504, 513, 3253, 3256, 3259, 3261, 3271, 3278, 3306, 3308, 3315, 3319, 3323, 3331, 3334, 3342, 3346, 3350, 3353, 3388, 3414, 4270, 4273, 4275, 4283, 4290, 4297, 4305, 4320, 4325, 4358, 4362, 4364, 4369, 4512]
  [2, 3, 4, 5, 10, 38, 39, 41, 47, 56, 66, 75, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 323, 325, 326, 327, 329, 332, 333, 343, 3255, 3258, 3260, 3264, 3265, 3267, 3273, 3274, 3275, 3277, 3290, 3292, 3300, 3309, 3316, 3322, 3326, 4268, 4269, 4271, 4272, 4274, 4276, 4277, 4278, 4279, 4280, 4284, 4286, 4287, 4288, 4291, 4293, 4296, 4299, 4300, 4301, 4304, 4314, 4315, 4318, 4321, 4327, 4331, 4343]
  :=
  ⟨_, Magma.mk model5_op, Finite.of_fintype _, by decideFin!⟩

