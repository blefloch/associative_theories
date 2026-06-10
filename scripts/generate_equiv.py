import json
from collections import defaultdict

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
with open("../data/long_classes.json", 'r') as f:
    long_classes = json.load(f)
with open("../data/eq_to_long_class.json", 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}
eq_to_long_class[4512] = [1, 4512]
with open("../data/associative_theories.json", 'r') as f:
    associative_theories = json.load(f)
with open("../data/explicitly_proven.json", 'r') as f:
    available_theorems = defaultdict(set)
    for k, v in json.load(f):
        available_theorems[tuple(k)] = set(v)

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

for eq_id in reps:
    available_theorems[eq_id, 4512] = eq_to_long_class[eq_id]

preamble = \
"""/- Generated file proving equivalence of conjunction representatives -/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.AssociativeTheoriesIndex
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.ConjecturesOneImpli
import associative_theories.ConjecturesTwo
import associative_theories.OneImpliDeduced

open ATIndex
open Conjectures

"""

#####################
def lean_have_one_eq(ids, id2):
    ids = sorted(set(ids))
    return (f"  have eq{id2} := Equation"
            + "_".join(map(str, ids))
            + f"_implies_Equation{id2} G eq"
            + " eq".join(map(str, ids)))

def lean_implies_long(clid, scl, lcl):
    lines = [f"private theorem AT{clid}_implies_long (G : Type*) [Magma G] (h : AssociativeTheory{clid} G) : AssociativeTheory{clid}_long G := by"]
    if scl == [4512]:
        return lines[0] + "\n  constructor\n  rw [Equation1]; intros; rfl\n  exact h"
    lines.append("  obtain ⟨" + ", ".join(f"eq{eq_id}" for eq_id in scl) + "⟩ := h")
    theorems = available_theorems[tuple(scl)]
    for c in theorems:
        if c not in scl:
            lines.append(lean_have_one_eq(scl, c))
    consequences = set()
    new_consequences = set(scl).union(theorems)
    while len(consequences) != len(new_consequences):
        consequences = new_consequences.copy()
        for a in consequences:
            for b in consequences:
                if a >= b:
                    continue
                for c in available_theorems[a, b, 4512]:
                    if c not in new_consequences:
                        new_consequences.add(c)
                        lines.append(lean_have_one_eq((a, b, 4512), c))
        for a in consequences:
            for c in eq_to_long_class[a]:
                if c not in new_consequences:
                    new_consequences.add(c)
                    lines.append(lean_have_one_eq((a, 4512), c))
    lines.append("  exact ⟨eq" + ", eq".join(map(str, lcl)) + "⟩")
    return "\n".join(lines)

def lean_equiv(clid, scl, lcl):
    return (lean_implies_long(clid, scl, lcl) + "\n\n"
            + f"private theorem AT{clid}_implied_by_long (G : Type*) [Magma G] : AssociativeTheory{clid}_long G -> AssociativeTheory{clid} G :=\n"
            + "fun ⟨" + ", ".join(map(lambda i: f"h{i}" if i in scl else "_", lcl)) + "⟩ => "
            + ("⟨" if clid > 1 else "") + ", ".join(map(lambda i: f"h{i}", scl)) + ("⟩" if clid > 1 else "") + "\n")

with open("../associative_theories/EarlyLongEquiv.lean", "w") as f:
    print(preamble, file=f)
    for at in associative_theories:
        print(lean_equiv(at["id"], at["early"], at["long"]), file=f)
    print('theorem AT_equiv (G : Type*) [Magma G] (ati : ATIndex) : (ATearly G ati) <-> (ATlong G ati) :=\n'
          + 'match ati with', file=f)
    for at in associative_theories:
        at_id = at['id']
        print(f'| at{at_id} => ⟨AT{at_id}_implies_long G, AT{at_id}_implied_by_long G⟩', file=f)
