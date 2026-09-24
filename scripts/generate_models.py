from find_equation_id import Equation
from ATP_utils import test_eq_with_magma
from countermodels import countermodel_list

# Start with the list of single-equation equivalence classes:
eqs_to_test = [1, 2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 40, 41, 43, 47, 56, 66, 75, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 323, 325, 326, 327, 329, 332, 333, 343, 411, 419, 429, 440, 477, 504, 513, 3253, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3271, 3273, 3274, 3275, 3277, 3278, 3290, 3292, 3300, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3346, 3350, 3353, 3388, 3414, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4283, 4284, 4286, 4287, 4288, 4290, 4291, 4293, 4296, 4297, 4299, 4300, 4301, 4304, 4305, 4314, 4315, 4318, 4320, 4321, 4325, 4327, 4331, 4343, 4358, 4362, 4364, 4369]
# Add associativity, which we will need to know about
eqs_to_test.append(4512)

def generate_model(index, t):
    mul_table = str([list(ti) for ti in t]).replace(' ', '')
    eqs_obeyed = []
    eqs_refuted = []
    for eq_id in eqs_to_test:
        if test_eq_with_magma(eq_id, t):
            eqs_obeyed.append(eq_id)
        else:
            eqs_refuted.append(eq_id)
    with open(f"../associative_theories/Countermodels/Model{index}.lean", "w") as f:
        print(f"""import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod

private def model{index}_op := finOpTable "{mul_table}"

theorem facts_from_model{index} :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
  {eqs_obeyed}
  {eqs_refuted}
  :=
  ⟨_, Magma.mk model{index}_op, Finite.of_fintype _, by decideFin!⟩
""", file=f)

with open("../associative_theories/Countermodels.lean", "w") as f:
    for i, t in enumerate(countermodel_list):
        print("model", i, end="     \r")
        generate_model(i, t)
        print(f"import associative_theories.Countermodels.Model{i}", file=f)
