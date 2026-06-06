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

def conjecture_preamble(how_many = "single", facts = False):
    preamble = ""
    if facts: preamble += "import equational_theories.FactsSyntax\n"
    preamble += "import equational_theories.Equations.All\n"
    preamble += f"\n/- Generated file collecting conjectures about {how_many} equations -/\n"
    preamble += "\nnamespace Conjectures\n"
    return preamble
def conjecture_postamble():
    return "\nend Conjectures\n"

###### Single equations

def one_conjecture(id1, id2):
    return f"theorem Equation{id1}_4512_implies_Equation{id2} (G : Type*) [Magma G]\n    (eq{id1} : Equation{id1} G) (eq4512 : Equation4512 G) : Equation{id2} G := sorry\n"

with open("../associative_theories/ConjecturesOneEquiv.lean", "w") as f:
    print(conjecture_preamble(), file=f)
    for cl in eq_classes:
        if len(cl) > 1:
            print(f"\n/- Equivalence of {cl} -/", file=f)
            for i in range(len(cl)):
                print(one_conjecture(cl[i - 1], cl[i]), file=f)
    print(conjecture_postamble(), file=f)

DG = nx.DiGraph()
edge_list = [(id1, id2) for id1, lcl in eq_to_long_class.items()
             for id2 in lcl if len({id1, id2, 4512}) == 3]
DG.add_edges_from(set(edge_list))
DGred = nx.transitive_reduction(DG)

with open("../associative_theories/ConjecturesOneImpli.lean", "w") as f:
    print(conjecture_preamble(), file=f)
    for id1, id2 in sorted(DGred.edges()):
        print(one_conjecture(id1, id2), file=f)
    print(conjecture_postamble(), file=f)

implication_proofs = []
for id1, id2 in sorted(set(DG.edges()).difference(DGred.edges())):
    implication_proofs.append(nx.shortest_path(DGred, source=id1, target=id2))

def call_conj(p1, p2):
    return f"Equation{p1}_4512_implies_Equation{p2} G eq{p1} eq4512"
def one_proof(p):
    theorem = f"theorem Equation{p[0]}_4512_implies_Equation{p[-1]} (G : Type*) [Magma G]\n"
    theorem += f"  (eq{p[0]} : Equation{p[0]} G) (eq4512 : Equation4512 G) : Equation{p[-1]} G := by"
    for i in range(len(p) - 2):
        theorem += f"\n  have eq{p[i + 1]} := " + call_conj(p[i], p[i + 1])
    theorem += "\n  exact " + call_conj(p[-2], p[-1]) + "\n"
    return theorem

def oneimplideduced_preamble():
    preamble = "import equational_theories.Equations.All\n"
    preamble += "import associative_theories.ConjecturesOneImpli\n\n"
    preamble += "/- Generated file for the single-equation implication graph -/\n\n"
    preamble += "open Conjectures\n\n"
    return preamble

with open("../associative_theories/OneImpliDeduced.lean", "w") as f:
    print(oneimplideduced_preamble(), file=f)
    print("theorem Equation4512_implies_Equation1 (G : Type*) [Magma G] (_ : Equation4512 G) : Equation1 G := by rw [Equation1]; intros; rfl\n", file=f)
    for p in implication_proofs:
        print(one_proof(p), file=f)

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

explicit_consequences = defaultdict(set)
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

def multi_conjecture(ids, id2):
    return (f"theorem Equation{'_'.join(map(str, ids))}_4512_implies_Equation{id2} (G : Type*) [Magma G]\n    "
            + " ".join(f"(h{eq_id} : Equation{eq_id} G)" for eq_id in ids + (4512,))
            + f" : Equation{id2} G := sorry\n")

# Add two explicit consequences by hand
explicit_consequences[307, 4284, 4321] = {4293}
explicit_consequences[307, 4321, 4369] = {4293}

with open("../associative_theories/ConjecturesTwo.lean", "w") as f:
    print(conjecture_preamble("pairs of"), file=f)
    for premises, kset in sorted(explicit_consequences.items()):
        for k in sorted(kset):
            print(multi_conjecture(premises, k), file=f)
    print(conjecture_postamble(), file=f)


###### For each class, ensure that the short class implies the long one
with open("../data/associative_conjunctions.json", "r") as f:
    representatives = json.load(f)

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

for d in representatives:
    clid = d["id"]
    scl = d["lexicographic"]
    lcl = d["long"]
    mcl = scl + list(explicit_consequences[tuple(scl[:-1])])
    consequences = get_pair_consequences(mcl)
    assert(sorted(consequences) == lcl)

######### Store the explicitly proven implications in a JSON file

with open("../data/explicitly_proven.json", "w") as f:
    print("[", file=f)
    for eq_id in sorted(DGred):
        if DGred[eq_id]:
            print('  ' + str([[eq_id, 4512], list(DGred[eq_id])]) + ',', file=f)
    #for id1, id2 in sorted(DGred.edges()):
    #    print('  ' + str([[id1, 4512], id2]) + ',', file=f)
    print(",\n".join('  ' + str([list(premises) + [4512], list(kset)])
                     for premises, kset in sorted(explicit_consequences.items()) if kset),
          file=f)
    print("]", file=f)
