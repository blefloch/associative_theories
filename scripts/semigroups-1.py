"""Find implications between conjunctions of semigroup laws

Using the mace4/Prover9 ATP and countermodels from the file
countermodels.py, this first finds all implications
between conjunctions of the 4694 magma equational laws under
the additional assumption of associativity (Equation 4512).
"""

from find_equation_id import all_eqs, Equation, shape_order
from ATP_utils import models, prove, test_eq_with_magma
from collections import defaultdict

try:
    from countermodels import *
except ModuleNotFoundError:
    with open("countermodels.py", "w") as f:
        print("""from ATP_utils import test_eq_with_magma

countermodel_list = []

def to_tuples(m):
    return tuple(tuple(mi) for mi in m)

def add_model(m):
    mag = to_tuples(m)
    if test_eq_with_magma(4512, mag):
        countermodel_list.append(mag)
    else:
        raise ValueError(mag)
""", file=f)
    from countermodels import *

one_has_model = {1: [True] * len(countermodel_list), 2: [False] * len(countermodel_list)}

def right_associative_shape(n):
    return (None, right_associative_shape(n - 1)) if n > 0 else None

def right_associate(shape):
    return right_associative_shape(shape_order(shape))

assoc_eq = "x*(y*z)=(x*y)*z."
one_to_rep = {1: 1, 2: 2} # maps eq id to eq id that is equivalent
one_rep = {1: 'x = x', 2: 'x = y'} # maps eq id (not equivalent to a lower one) to their str used for ATP
consequences = defaultdict(set, {(1,): {1}, (2,): {1, 2}}) # maps (ordered tuples of eq id) to the (set of eq id) they imply
unknown_consequences = defaultdict(set) # same structure as consequences

def one_implication(eqA_id, eqA_str, eqB_id, eqB_str):
    return aux_implication((eqA_id,), eqA_str+". "+assoc_eq, eqB_id, eqB_str+".")

def multi_implication(eqs_id, eqB_id):
    extra1 = ". ".join(one_rep[i] for i in eqs_id) + ". " + assoc_eq
    extra2 = one_rep[eqB_id] + "."
    return aux_implication(tuple(eqs_id), extra1, eqB_id, extra2)

def aux_implication(eqs_id, extra1, eqB_id, extra2):
    implies = None
    for i, m in enumerate(countermodel_list):
        if all(one_has_model[j][i] for j in eqs_id) and not one_has_model[eqB_id][i]:
            implies = False
            break
    if implies is None:
        if prove([], [], extra1=extra1, extra2=extra2):
            implies = True
        else:
            mods = models([], [], extra0="assign(iterate_up_to, 27). assign(max_models, 1).", extra1=extra1, extra2=extra2, max_seconds=10)
            if mods:
                m = to_tuples(mods[0])
                print(f"add_model({m})")
                add_model(m)
                for eq_id, v in one_has_model.items():
                    v.append(test_eq_with_magma(eq_id, m))
                implies = False
    if implies is True:
        consequences[eqs_id].add(eqB_id)
    elif implies is None:
        print(f"Unknown implication {eqs_id} ({extra1}) to {eqB_id} ({extra2})")
        unknown_consequences[eqs_id].add(eqB_id)
    return implies

# Find equivalence classes and implications for single equations

for eq1_id in range(3, 4695):
    eq1 = Equation.from_id(eq1_id)
    eq1_str = str(eq1).replace("◇", "*")
    print(eq1_id, eq1_str, end="   \r")
    # The first line may build a broken equation such as x*(y*z)=x*(z*z), then normalized to x*(y*y)=x*(z*y) by the line below
    eq1_right_assoc = Equation(right_associate(eq1.lhs_shape), right_associate(eq1.rhs_shape), eq1.rhyme)
    eq1_right_assoc = Equation.from_str(str(eq1_right_assoc))
    i = max(eq1_right_assoc.id, 1) # tautological eqs have id 0, equivalent to equation 1
    if i < eq1_id:
        one_to_rep[eq1_id] = one_to_rep[i]
    elif i > eq1_id:
        raise ValueError(f"Right-associating equation {eq1_id} ({eq1_str}) gave the larger equation {i} ({eq1_right_assoc})")
    else:
        one_has_model[eq1_id] = [test_eq_with_magma(eq1, m) for m in countermodel_list]
        for eq2_id, eq2_str in one_rep.items():
            eq1_implies_eq2 = one_implication(eq1_id, eq1_str, eq2_id, eq2_str)
            eq2_implies_eq1 = one_implication(eq2_id, eq2_str, eq1_id, eq1_str)
            if eq1_implies_eq2 is True and eq2_implies_eq1 is True:
                one_to_rep[eq1_id] = eq2_id
                break
            if eq1_implies_eq2 in [True, None] and eq2_implies_eq1 in [True, None]:
                print(f"Unknown equivalence {eq1_id} vs {eq2_id}")
        if eq1_id in one_to_rep:
            del one_has_model[eq1_id]
            consequences.pop((eq1_id,), None)
            unknown_consequences.pop((eq1_id,), None)
        else:
            one_to_rep[eq1_id] = eq1_id
            one_rep[eq1_id] = eq1_str
            consequences[(eq1_id,)].add(eq1_id)

print(len(one_rep), sorted(one_rep))
if unknown_consequences:
    print(dict(unknown_consequences))
# print(one_to_rep)

consequences = defaultdict(set, {k: v.intersection(one_rep) for k, v in consequences.items()})

multi_rep = set((i,) for i, s in one_rep.items()) # set of non-diminishable (ordered tuples of eq id)
multi_to_rep = {} # maps (ordered tuples of eq id) (obtained by appending a one_rep to a multi_rep) to their representative
pending = [(i,) for i in sorted(one_rep)]
while pending:
    eqsA = pending.pop(0)
    for moreA in one_rep:
        if moreA <= eqsA[-1]:
            continue
        fullA = eqsA + (moreA,)
        print(f"current {fullA}; pending {len(pending)}; found {len(multi_rep)}", end="  \r")
        for a, i in enumerate(fullA):
            partA = fullA[:a] + fullA[a + 1:]
            if i in consequences[partA]:
                multi_to_rep[fullA] = partA
        if fullA in multi_to_rep:
            continue
        [multi_implication(fullA, j) for j in one_rep] # updates (unknown_)consequences[fullA]
        for eqsB in multi_rep:
            if consequences[fullA].issuperset(eqsB) and consequences[eqsB].issuperset(fullA):
                multi_to_rep[fullA] = eqsB
                break
            if (all(j in consequences[fullA] or j in unknown_consequences[fullA] for j in eqsB)
                and all(i in consequences[eqsB] or i in unknown_consequences[eqsB] for i in fullA)):
                print(f"Unknown equivalence {fullA} vs {eqsB}")
        if fullA in multi_to_rep:
            # We found an equivalent, delete useless data
            consequences.pop(fullA, None)
            unknown_consequences.pop(fullA, None)
        else:
            # The new equivalence class may lead to further conjunctions
            multi_to_rep[fullA] = fullA
            multi_rep.add(fullA)
            pending.append(fullA)
            if (len(multi_rep) % 100) == 0:
                print(sorted(multi_rep))

print(len(multi_rep), sorted(multi_rep, key=(lambda x:(len(x), x))))

long_classes = sorted(tuple(sorted(v.union([4512]))) for v in consequences.values() if v)
eq_to_long_class = {k[0]: tuple(sorted(v.union([4512]))) for k, v in consequences.items() if len(k) == 1 and v}

with open("one_to_rep.py", "w") as f:
    print(f"one_to_rep = {one_to_rep}", file=f)

with open("../data/long_classes.json", "w") as f:
    f.write('[\n    ' + ',\n    '.join(str(list(c)) for c in long_classes) + '\n]\n')

with open("../data/eq_to_long_class.json", "w") as f:
    f.write('{\n    ' + ',\n    '.join(f'"{k}": {list(v)}' for k, v in eq_to_long_class.items()) + '\n}\n')
