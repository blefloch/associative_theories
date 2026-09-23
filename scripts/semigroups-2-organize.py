import json
from collections import defaultdict
from find_equation_id import Equation, all_eqs, shape_order, canonicalize_rhyme
from semigroups_to_rep_out import one_to_rep
from collections import defaultdict

def right_shape_n(n):
    return (None, right_shape_n(n - 1)) if n > 0 else None
def right_shape(shape):
    return right_shape_n(shape_order(shape))
def right_associate(eq):
    return Equation(right_shape(eq.lhs_shape), right_shape(eq.rhs_shape), eq.rhyme)
def right_dual(eq):
    return right_associate(eq.dual())

eqs_found = {"x = x": 1}
for order in range(5):
    for eq in all_eqs(order):
        if eq.lhs_shape != right_shape(eq.lhs_shape):
            continue
        if eq.rhs_shape != right_shape(eq.rhs_shape):
            continue
        semigroup_eq = str(eq).replace("(", "").replace(")", "")
        lhs, rhs = semigroup_eq.split(" = ")
        if lhs != rhs and semigroup_eq not in eqs_found:
            eqs_found[semigroup_eq] = eq.id

associative_eq_ids = list(eqs_found.values())
equiv_class = defaultdict(set)
for eq_id in associative_eq_ids:
    equiv_class[one_to_rep[eq_id]].add(eq_id)

with open("../data/associative_equations.txt", "w") as f:
    for eq_str in eqs_found.keys():
        print(eq_str, file=f)

with open("../data/associative_equation_ids.json", "w") as f:
    print(associative_eq_ids, file=f)

with open("../data/associative_equation_classes.json", "w") as f:
    print("[", file=f)
    print(",\n".join(f"    {sorted(eq_class)}"
                     for eq_id, eq_class in sorted(equiv_class.items())), file=f)
    print("]", file=f)

assert(len(set.union(*list(equiv_class.values()))) == 653)
assert(sum(len(ec) for ec in equiv_class.values()) == 653)

###################
# Admittedly it is sub-optimal to reload a json file we just wrote out

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

json_items = []
for i, (ec, lc) in enumerate(early_class_to_long_class.items()):
    dc = [right_dual(Equation.from_id(i)).id for i in ec if i != 4512]
    dec = long_class_to_early_class[tuple(find_class(dc))]
    json_items.append(f'  {{"id": {i + 1}, "early": {list(ec)}, "long": {list(lc)}, "dual": {list(dec)}}}')

with open("../data/associative_theories.json", "w") as f:
    print("[", file=f)
    print(",\n".join(json_items), file=f)
    print("]", file=f)
