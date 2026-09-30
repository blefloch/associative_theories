import json
from collections import defaultdict

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
with open("../data/long_classes.json", 'r') as f:
    long_classes = json.load(f)

with open("../data/associative_theories.json", 'r') as f:
    associative_theories = json.load(f)

preamble = "/- Generated file defining the conjunction representatives -/\n\n"
preamble += "import equational_theories.Equations.All\n"
preamble += "import equational_theories.FactsSyntax\n"

with open("../associative_theories/AssociativeTheoriesIndex.lean", "w") as f:
    print(preamble + '\n', file=f)
    print('inductive ATIndex\n' + ''.join(f'| at{at["id"]} ' for at in associative_theories), file=f)

preamble += "import associative_theories.AssociativeTheoriesIndex\n"
preamble += "open ATIndex\n"

with open("../associative_theories/AssociativeTheoriesEarly.lean", "w") as f:
    print(preamble + '\n', file=f)
    for at in associative_theories:
        print(f'def AssociativeTheory{at["id"]} (G: Type*) [Magma G] := Facts G [{", ".join(map(str, at["early"]))}] []', file=f)
    print('\ndef ATearly : ATIndex → ∀(G: Type*) [Magma G], Prop', file=f)
    for at in associative_theories:
        at_id = at["id"]
        print(f'| at{at_id} => AssociativeTheory{at_id}', file=f)

with open("../associative_theories/AssociativeTheoriesLong.lean", "w") as f:
    print(preamble + '\n', file=f)
    for at in associative_theories:
        print(f'def AssociativeTheory{at["id"]}_long (G: Type*) [Magma G] := Facts G [{", ".join(map(str, at["long"]))}] []', file=f)
    print('\ndef ATlong : ATIndex → ∀(G: Type*) [Magma G], Prop', file=f)
    for at in associative_theories:
        at_id = at["id"]
        print(f'| at{at_id} => AssociativeTheory{at_id}_long', file=f)


####

preamble = "/- Generated file defining the equation index -/\n\n"
preamble += "import equational_theories.Equations.All\n"
preamble += "import equational_theories.FactsSyntax\n"

with open("../associative_theories/EquationIndex.lean", "w") as f:
    all_eqs = sorted(set(reps).union({4512}))
    print(preamble + '\n', file=f)
    print('inductive EQIndex\n'
          + ''.join(f'| eq{eqid} ' for eqid in all_eqs),
          file=f)
    print('\ndef EQeq : EQIndex → ∀(G: Type*) [Magma G], Prop\n'
          + ''.join(f'| .eq{eqid} => Equation{eqid}\n' for eqid in all_eqs),
          file=f)
