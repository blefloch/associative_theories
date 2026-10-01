from find_equation_id import Equation
from ATP_utils import test_eq_with_magma
from countermodels import countermodel_list
import json

with open('../data/associative_theories.json', 'r') as f:
    associative_theories = json.load(f)

# Start with the list of single-equation equivalence classes:
eqs_to_test = [1, 2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 40, 41, 43, 47, 56, 66, 75, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 323, 325, 326, 327, 329, 332, 333, 343, 411, 419, 429, 440, 477, 504, 513, 3253, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3271, 3273, 3274, 3275, 3277, 3278, 3290, 3292, 3300, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3346, 3350, 3353, 3388, 3414, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4283, 4284, 4286, 4287, 4288, 4290, 4291, 4293, 4296, 4297, 4299, 4300, 4301, 4304, 4305, 4314, 4315, 4318, 4320, 4321, 4325, 4327, 4331, 4343, 4358, 4362, 4364, 4369]
# Add associativity, which we will need to know about
eqs_to_test.append(4512)

model_eqs = []
for t in countermodel_list:
    mul_table = str([list(ti) for ti in t]).replace(' ', '')
    eqs_obeyed = []
    eqs_refuted = []
    for eq_id in eqs_to_test:
        if test_eq_with_magma(eq_id, t):
            eqs_obeyed.append(eq_id)
        else:
            eqs_refuted.append(eq_id)
    model_eqs.append([eqs_obeyed, eqs_refuted])

def generate_model(index, t):
    size = len(t)
    mul_table = str([list(ti) for ti in t]).replace(' ', '')
    eqs_obeyed, eqs_refuted = model_eqs[index]
    with open(f"../associative_theories/Countermodels/Model{index}.lean", "w") as f:
        print(f"""import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly

private def model{index}_op := finOpTable "{mul_table}"
private def model{index} : Magma (Fin {size}) where op := model{index}_op
private instance : Magma (Fin {size}) := model{index}
"""
              , file=f)
        for eq in eqs_obeyed:
            print(f'private theorem model{index}_eq{eq} : Equation{eq} (Fin {size}) := by decideFin!', file=f)
        for eq in eqs_refuted:
            print(f'private theorem not_model{index}_eq{eq} : Not (Equation{eq} (Fin {size})) := by decideFin!', file=f)
        for at in associative_theories:
            if set(at['early']).issubset(eqs_obeyed):
                print(f'\ntheorem model{index}_at{at["id"]} : AssociativeTheory{at["id"]} (Fin {size}) :=', file=f)
                if len(at['early']) == 1:
                    print(f'  model{index}_eq{at["early"][0]}', file=f)
                else:
                    print('  ⟨' + ', '.join(f'model{index}_eq{eq}' for eq in at['early']) + '⟩', file=f)
            else:
                print(f'\ntheorem not_model{index}_at{at["id"]} : Not (AssociativeTheory{at["id"]} (Fin {size})) := by', file=f)
                i = 0
                while at['early'][i] in eqs_obeyed:
                    i += 1
                    print(f'  refine not_and_of_not_right _ ?_', file=f)
                print(f'  refine not_and_of_not_left _ ?_', file=f)
                print(f'  exact not_model{index}_eq{at["early"][i]}', file=f)

with open("../associative_theories/Countermodels.lean", "w") as f:
    for i, t in enumerate(countermodel_list):
        print("model", i, end="     \r")
        generate_model(i, t)
        print(f"import associative_theories.Countermodels.Model{i}", file=f)

with open(f'../associative_theories/NonImplications.lean', 'w') as f:
    print('/- Generated file proving non-implications between associative theories -/\n', file=f)
    for at in associative_theories:
        print(f'import associative_theories.NonImplications.NonImplications{at["id"]}', file=f)
    print('''
theorem AT_not_implies (atid : ATIndex) :
  (atid2 : ATIndex) -> (hh : Not (AT_impliesQ atid atid2)) ->
  ∃ (G : Type) (_ : Magma G) (_ : Finite G), (ATearly atid G) ∧ Not (ATearly atid2 G) :=
match atid with''', file=f)
    for at in associative_theories:
        print(f'| .at{at["id"]} => AT{at["id"]}_not_implies', file=f)

for at in associative_theories:
    print('Associative theory', at['id'], end='\r')
    with open(f'../associative_theories/NonImplications/NonImplications{at["id"]}.lean', 'w') as f:
        usable_models = {}
        for i, t in enumerate(countermodel_list):
            eqs_obeyed, eqs_refuted = model_eqs[i]
            if set(at['long']).issubset(eqs_obeyed):
                usable_models[i] = (t, eqs_obeyed, eqs_refuted)
        print(f'''/- Generated file proving non-implications from the associative theory {at["id"]} -/

import Mathlib.Data.Finite.Prod
import associative_theories.AssociativeTheoriesEarly
import associative_theories.ImplicationsAT
import associative_theories.Countermodels
''',
            file=f)
        print(f'theorem AT{at["id"]}_not_implies (atid : ATIndex) (hh : Not (AT{at["id"]}_impliesQ atid)) :', file=f)
        print(f'  ∃ (G : Type) (_ : Magma G) (_ : Finite G), AssociativeTheory{at["id"]} G ∧ Not (ATearly atid G) :=', file=f)
        print('match atid with', file=f)
        for at2 in associative_theories:
            if set(at2['long']).issubset(at['long']):
                print(f'| .at{at2["id"]} => (hh True.intro).elim', file=f)
            else:
                for i, (t, eqs_obeyed, eqs_refuted) in usable_models.items():
                    if not set(at2['long']).issubset(eqs_obeyed):
                        print(f'| .at{at2["id"]} => ⟨_, _, Finite.of_fintype _, model{i}_at{at["id"]}, not_model{i}_at{at2["id"]}⟩', file=f)
                        break
