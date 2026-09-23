from find_equation_id import Equation, all_eqs, shape_order, canonicalize_rhyme
from semigroups_to_rep_out import one_to_rep
from collections import defaultdict

def right_associative_shape(n):
    return (None, right_associative_shape(n - 1)) if n > 0 else None

def right_associate(shape):
    return right_associative_shape(shape_order(shape))

eqs_found = {"x = x": 1}
for order in range(5):
    for eq in all_eqs(order):
        lhs_shape = right_associate(eq.lhs_shape)
        rhs_shape = right_associate(eq.rhs_shape)
        rhyme = eq.rhyme
        if lhs_shape == rhs_shape:
            m = 1 + shape_order(lhs_shape)
            rhyme = min(rhyme, canonicalize_rhyme(rhyme[m:] + rhyme[:m]))
        eq_right = Equation(lhs_shape, rhs_shape, rhyme)
        semigroup_eq = str(eq_right).replace("(", "").replace(")", "")
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
