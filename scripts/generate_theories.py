import json
from collections import defaultdict

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
with open("../data/long_classes.json", 'r') as f:
    long_classes = json.load(f)

with open("../data/associative_theories.json", 'r') as f:
    associative_theories = json.load(f)

preamble = "import equational_theories.Equations.All\n"
preamble += "import equational_theories.FactsSyntax\n\n"
preamble += "/- Generated file defining the conjunction representatives -/\n\n"

with open("../associative_theories/AssociativeTheoriesEarly.lean", "w") as f:
    print(preamble, file=f)
    for at in associative_theories:
        print(f'def AssociativeTheory{at["id"]} (G: Type*) [Magma G] := Facts G [{", ".join(map(str, at["early"]))}] []', file=f)

with open("../associative_theories/AssociativeTheoriesLong.lean", "w") as f:
    print(preamble, file=f)
    for at in associative_theories:
        print(f'def AssociativeTheory{at["id"]}_long (G: Type*) [Magma G] := Facts G [{", ".join(map(str, at["long"]))}] []', file=f)
