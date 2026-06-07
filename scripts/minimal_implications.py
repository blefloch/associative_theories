import json
import networkx as nx
from collections import defaultdict

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
with open("../data/eq_to_long_class.json", 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}
eq_to_long_class[4512] = [1, 4512]
long_class_to_eq = {tuple(v): k for k, v in eq_to_long_class.items()}
simple_long_classes = list(eq_to_long_class.values())
with open("../data/long_classes.json", 'r') as f:
    long_classes = json.load(f)
with open("../data/associative_theories.json", "r") as f:
    associative_theories = json.load(f)

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

###### Single equations

explicit_consequences = defaultdict(set)

DG = nx.DiGraph()
edge_list = [(id1, id2) for id1, lcl in eq_to_long_class.items()
             for id2 in lcl if len({id1, id2, 4512}) == 3]
DG.add_edges_from(set(edge_list))
DGred = nx.transitive_reduction(DG)

for id1 in sorted(DGred):
    if DGred[id1]:
        explicit_consequences[id1,] = set(DGred[id1])

###### Pairs of equations
known_consequences = {}
def calculate_consequences(base):
    consequences = set()
    new_consequences = set(base)
    while len(consequences) != len(new_consequences):
        consequences = new_consequences.copy()
        for a in consequences:
            for b in consequences:
                if a >= b:
                    continue
                new_consequences.update(known_consequences.get((a, b), {}))
    return consequences

edge_list = []
for i in reps:
    for j in reps:
        if i >= j:
            continue
        print(i, j, end="\r")
        known_consequences[i, j] = calculate_consequences({4512}.union(eq_to_long_class[i], eq_to_long_class[j]))
        set_ij = set(find_class([i, j]))
        pending = set_ij.difference(known_consequences[i, j])
        while pending:
            k = min(pending)
            pending.remove(k)
            edge_list.append((i, j, k))
            known_consequences[i, j].update(eq_to_long_class[k])
            known_consequences[i, j] = calculate_consequences(known_consequences[i, j])
            pending.difference_update(known_consequences[i, j])

for i, j, k in edge_list:
    explicit_consequences[i, j].add(k)

for i, j, k in edge_list:
    print(i, j, k, end="\r")
    explicit_consequences[i, j].remove(k)
    consequences = set()
    new_consequences = {4512}.union(eq_to_long_class[i], eq_to_long_class[j])
    while len(consequences) != len(new_consequences):
        consequences = new_consequences.copy()
        for a in consequences:
            for b in consequences:
                if a >= b:
                    continue
                new_consequences.update(explicit_consequences[a, b])
        for a in consequences:
            new_consequences.update(eq_to_long_class[a])
    if k not in consequences:
        explicit_consequences[i, j].add(k)

# Add by hand two explicit consequences needed for early-long equivalence
explicit_consequences[307, 4284, 4321] = {4293}
explicit_consequences[307, 4321, 4369] = {4293}

# Add by hand some explicit consequences needed for other implications
explicit_consequences[307, 4290, 4291] = {4283}
explicit_consequences[307, 4293, 4314] = {4283}
explicit_consequences[307, 4293, 4320] = {4283}
explicit_consequences[307, 4290, 4321] = {4284}
explicit_consequences[307, 4283, 4343] = {4284}
explicit_consequences[307, 4291, 4343] = {4283}
explicit_consequences[307, 4293, 4343] = {4284}
explicit_consequences[411, 4283, 4290] = {43}

for premises, kset in explicit_consequences.items():
    assert(kset.issubset(find_class(premises)))

######### Store the explicitly proven implications in a JSON file

with open("../data/explicitly_proven.json", "w") as f:
    print("[", file=f)
    print(",\n".join('  ' + str([list(premises) + [4512], sorted(kset)])
                     for premises, kset in sorted(explicit_consequences.items()) if kset),
          file=f)
    print("]", file=f)

###### For each class, ensure that the short class implies the long one

pair_to_long_class = {}
for a in reps + [4512]:
    for b in reps + [4512]:
        if a >= b:
            continue
        pair_to_long_class[a, b] = find_class((a, b))

def get_pair_consequences(eq_set):
    consequences = set()
    new_consequences = set(eq_set)
    while len(consequences) != len(new_consequences):
        consequences = new_consequences.copy()
        for a in consequences:
            new_consequences.update(eq_to_long_class[a])
        for a in consequences:
            for b in consequences:
                if a >= b:
                    continue
                new_consequences.update(pair_to_long_class[a, b])
    return sorted(consequences)

for at in associative_theories:
    clid = at["id"]
    scl = at["early"]
    lcl = at["long"]
    mcl = scl + list(explicit_consequences[tuple(scl[:-1])])
    consequences = get_pair_consequences(mcl)
    assert(sorted(consequences) == lcl)

###### For each equation plus class, their conjunction needs to be equivalent to a known class

long_explicit = [set(premises) for premises in explicit_consequences.keys() if len(premises) >= 3]
print("                ", end="\r")
for eq_id in reps:
    print(eq_id, end="\r")
    for at in associative_theories:
        lcl = at["long"]
        if eq_id in lcl:
            continue
        candidate = get_pair_consequences(lcl + [eq_id])
        actual = find_class(candidate)
        if len(candidate) == len(actual):
            continue
        for s in long_explicit:
            if s.issubset(candidate):
                candidate = get_pair_consequences(candidate + list(explicit_consequences[tuple(sorted(s))]))
        if len(candidate) == len(actual):
            continue
        print(eq_id, at["early"], candidate, actual, sorted(set(actual).difference(candidate)))
