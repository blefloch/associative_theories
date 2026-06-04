from find_equation_id import Equation, all_eqs
from semigroups_to_rep_out import one_to_rep
from collections import defaultdict

eqs_found = {"x = x": 1}
for order in range(5):
    for eq in all_eqs(order):
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

assert(len(set.union(*list(equiv_class.values()))) == 739)
assert(sum(len(ec) for ec in equiv_class.values()) == 739)
