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
with open("../data/explicitly_proven.json", "r") as f:
    explicitly_proven = json.load(f)

available_theorems = defaultdict(set)
for k, v in explicitly_proven:
    available_theorems[tuple(sorted(k))] = set(v)
for eq_id in reps:
    available_theorems[eq_id, 4512] = eq_to_long_class[eq_id]

long_class_to_at = {}
for at in associative_theories:
    long_class_to_at[tuple(at["long"])] = at

long_explicit = [tuple(sorted(premises)) for premises, _ in explicitly_proven if len(premises) >= 4]

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

preamble = \
"""import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.ConjecturesOneImpli
import associative_theories.ConjecturesTwo
import associative_theories.OneImpliDeduced
import associative_theories.EarlyLongEquiv

/- Generated file proving equivalence of conjunction representatives -/

open Conjectures

"""

#####################
def lean_have_one_eq(ids, id2):
    ids = sorted(set(ids))
    return (f"  have eq{id2} := Equation"
            + "_".join(map(str, ids))
            + f"_implies_Equation{id2} G eq"
            + " eq".join(map(str, ids)))

def lean_eq_list(eqs, prefix="h"):
    if len(eqs) > 1:
        return "⟨" + ", ".join(map(lambda x: prefix + str(x), eqs)) + "⟩"
    return prefix + str(eqs[0])

def lean_conj_implies_at(at1, id2, at3):
    at1_id = at1["id"]
    at1_long = at1["long"]
    at3_id = at3["id"]
    lines = [f"theorem AT{at1_id}_Equation{id2}_implies_AT{at3_id} (G : Type*) [Magma G] (h : (AssociativeTheory{at1_id} G) ∧ (Equation{id2} G)) : AssociativeTheory{at3_id} G := by"]
    lines.append(f"  obtain ⟨h1, eq{id2}⟩ := h")
    if at3_id == at1_id:
        lines.append("  exact h1")
        return "\n".join(lines)
    lines.append("  obtain ⟨"
                 + ", ".join(f"eq{eq_id}" for eq_id in at1_long)
                 + f"⟩ := AT{at1_id}_implies_long G h1")
    proofs = []
    available = set(at1_long)
    available.add(id2)
    consequences = set()
    new_consequences = set(available)
    while len(consequences) != len(new_consequences):
        consequences = new_consequences.copy()
        for a in consequences:
            for b in consequences:
                if a >= b:
                    continue
                for c in available_theorems[a, b, 4512]:
                    if c not in new_consequences:
                        new_consequences.add(c)
                        proofs.append(((a, b, 4512), c))
        for a in consequences:
            for c in eq_to_long_class[a]:
                if c not in new_consequences:
                    new_consequences.add(c)
                    proofs.append(((a, 4512), c))
        for le in long_explicit:
            if new_consequences.issuperset(le):
                theorems = available_theorems[le]
                for c in theorems:
                    if c not in new_consequences:
                        new_consequences.add(c)
                        proofs.append((le, c))
    requirements = defaultdict(set)
    for premises, c in proofs:
        requirements[c].update(premises)
    needed = set()
    new_needed = set(at3["early"])
    while len(needed) != len(new_needed):
        needed = new_needed.copy()
        for c in needed:
            new_needed.update(requirements[c])
    for premises, c in proofs:
        if c in needed:
            lines.append(lean_have_one_eq(premises, c))
    lines.append("  exact " + lean_eq_list(at3["early"], "eq"))
    return "\n".join(lines)

def lean_conj_equiv(at1, id2, at3):
    at1_id = at1["id"]
    at3_id = at3["id"]
    return (lean_conj_implies_at(at1, id2, at3) + "\n\n"
            + f"theorem AT{at1_id}_Equation{id2}_implied_by_AT{at3_id} (G : Type*) [Magma G] (h : AssociativeTheory{at3_id} G) : (AssociativeTheory{at1_id} G) ∧ (Equation{id2} G) := by\n"
            + "  obtain " + lean_eq_list(at3["long"]) + f" := AT{at3_id}_implies_long G h\n"
            + f"  exact ⟨" + lean_eq_list(at1["early"]) + f", h{id2}⟩\n\n"
            + f"theorem AT{at1_id}_Equation{id2}_equiv_AT{at3_id} (G : Type*) [Magma G] : ((AssociativeTheory{at1_id} G) ∧ (Equation{id2} G)) <-> AssociativeTheory{at3_id} G :=\n"
            + f"  Iff.intro (AT{at1_id}_Equation{id2}_implies_AT{at3_id} G) (AT{at1_id}_Equation{id2}_implied_by_AT{at3_id} G)")

to_prove = []
for at in associative_theories:
    print(at["id"], end="\r")
    for eq_id in reps:
        lcl = at["long"]
        goals_at = long_class_to_at[tuple(find_class(at["early"] + [eq_id]))]
        if goals_at["id"] == at["id"]:
            continue
        to_prove.append((at, eq_id, goals_at))

#tally = defaultdict(int)
#for (at1, id2, at3) in to_prove:
#    tally[at3["id"]] += 1
#print(sorted(tally.items()))
#quit()

for atid in range(1, 457):
    print(atid, end="    \r")
    with open(f"../associative_theories/Conjunction/Conjunction{atid}.lean", "w") as f:
        print(preamble, file=f)
        for (at1, id2, at3) in to_prove:
            if at1["id"] == atid:
                print(lean_conj_equiv(at1, id2, at3) + "\n", file=f)
