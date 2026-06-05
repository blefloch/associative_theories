import json
from collections import defaultdict

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
with open("../data/long_classes.json", 'r') as f:
    long_classes = json.load(f)


def find_class(eq_set):
    eq_set = set(eq_set)
    s = set(reps)
    for c in long_classes:
        if eq_set.issubset(c):
            s = s.intersection(c)
    result = sorted(s) + [4512]
    if result in long_classes:
        return result
    else:
        raise ValueError(result)

long_class_to_early_class = {}
early_class_to_long_class = {}

long_class_to_early_class[tuple(find_class({4512}))] = [4512]
early_class_to_long_class[(4512,)] = find_class({4512})

for imax in reps:
    print(imax, end="\r")
    for ecl in list(early_class_to_long_class.keys()):
        ecli = tuple(sorted(ecl + (imax,)))
        lcli = tuple(find_class(ecli))
        if lcli not in long_class_to_early_class:
            long_class_to_early_class[lcli] = ecli
            early_class_to_long_class[ecli] = lcli

#print(early_class_to_long_class)
#print([ec[:-1] for ec in early_class_to_long_class.keys()])
json_items = []
for i, (ec, lc) in enumerate(early_class_to_long_class.items()):
    json_items.append(f'  {{"id": {i + 1}, "lexicographic": {list(ec)}, "long": {list(lc)}}}')

with open("../data/associative_conjunctions.json", "w") as f:
    print("[", file=f)
    print(",\n".join(json_items), file=f)
    print("]", file=f)

preamble = "import equational_theories.Equations.All\n"
preamble += "import equational_theories.FactsSyntax\n\n"
preamble += "/- Generated file defining the conjunction representatives -/\n\n"

with open("../associative_theories/ConjunctionRepresentatives.lean", "w") as f:
    print(preamble, file=f)
    for i, (ec, lc) in enumerate(early_class_to_long_class.items()):
        print(f'def ConjunctionClass{i + 1} (G: Type*) [Magma G] := Facts G [{", ".join(map(str, ec))}] []', file=f)

with open("../associative_theories/ConjunctionRepresentativesLong.lean", "w") as f:
    print(preamble, file=f)
    for i, (ec, lc) in enumerate(early_class_to_long_class.items()):
        print(f'def ConjunctionClass{i + 1}_long (G: Type*) [Magma G] := Facts G [{", ".join(map(str, lc))}] []', file=f)
