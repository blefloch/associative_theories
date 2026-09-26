import json
import networkx as nx
from collections import defaultdict

with open('../data/associative_equation_classes.json', 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
all_eqs = list(reps) + [4512]
with open('../data/eq_to_long_class.json', 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}
eq_to_long_class[4512] = [1, 4512]
long_class_to_eq = {tuple(v): k for k, v in eq_to_long_class.items()}
simple_long_classes = list(eq_to_long_class.values())
with open('../data/long_classes.json', 'r') as f:
    long_classes = json.load(f)
with open('../data/associative_theories.json', 'r') as f:
    associative_theories = json.load(f)
with open('../data/explicitly_proven.json', 'r') as f:
    explicitly_proven = json.load(f)

available_theorems = defaultdict(set)
for k, v in explicitly_proven:
    available_theorems[tuple(sorted(k))] = set(v)
for eq_id in reps:
    available_theorems[eq_id, 4512] = eq_to_long_class[eq_id]

long_class_to_at = {}
atid_to_at = {}
for at in associative_theories:
    long_class_to_at[tuple(at['long'])] = at
    atid_to_at[at['id']] = at

long_explicit = [tuple(sorted(premises)) for premises, _ in explicitly_proven if len(premises) >= 4]

def find_class(eq_set):
    eq_set = set(eq_set)
    s = set(all_eqs)
    for c in long_classes:
        if eq_set.issubset(c):
            s = s.intersection(c)
    result = sorted(s)
    if result in long_classes:
        return result
    else:
        raise ValueError(result)

preamble = \
'''/- Generated file proving equivalence of conjunction representatives -/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.EquationIndex
import associative_theories.AssociativeTheoriesIndex
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.VampireProvenOne
import associative_theories.VampireProvenTwo
import associative_theories.OneImpliDeduced
import associative_theories.EarlyLongEquiv
import associative_theories.ImplicationsAT

open EQIndex
open ATIndex
open VampireProven

set_option maxHeartbeats 1000000

'''

#####################
def lean_have_one_eq(ids, id2):
    ids = sorted(set(ids))
    return (f'  have h{id2} := Equation'
            + '_'.join(map(str, ids))
            + f'_implies_Equation{id2} G h'
            + ' h'.join(map(str, ids)))

def lean_eq_list(eqs, prefix='h'):
    if len(eqs) > 1:
        return '⟨' + ', '.join(map(lambda x: prefix + str(x), eqs)) + '⟩'
    return prefix + str(eqs[0])

def lean_conj_implies_at(at1, id2, at3):
    at1_id = at1['id']
    at1_long = at1['long']
    at3_id = at3['id']
    lines = [f'private theorem AT{at1_id}_Equation{id2}_implies (G : Type*) [Magma G] (h : (AssociativeTheory{at1_id} G) ∧ (Equation{id2} G)) : AssociativeTheory{at3_id} G := by']
    lines.append(f'  obtain ⟨hh, h{id2}⟩ := h')
    if at3_id == at1_id:
        lines.append('  exact hh')
        return '\n'.join(lines)
    lines.append(f'  obtain ⟨g, _⟩ := AT_equiv G at{at1_id}')
    lines.append('  obtain ' + lean_eq_list(at1_long) + ' := g hh')
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
    new_needed = set(at3['early'])
    while len(needed) != len(new_needed):
        needed = new_needed.copy()
        for c in needed:
            new_needed.update(requirements[c])
    for premises, c in proofs:
        if c in needed:
            lines.append(lean_have_one_eq(premises, c))
    lines.append('  exact ' + lean_eq_list(at3['early'], 'h'))
    return '\n'.join(lines)

def lean_conj_map(at1, pairs):
    at1_id = at1['id']
    return (f'def conj{at1_id} : EQIndex → ATIndex\n'
            + ''.join(f'| eq{id2} => at{at3["id"]}\n' for (id2, at3) in pairs))

def lean_conj_theorem(at1, pairs):
    at1_id = at1['id']
    return (f'theorem AT{at1_id}_conj_implied (eqid : EQIndex) (G: Type*) [Magma G] (h : ATearly G (conj{at1_id} eqid)) : (AssociativeTheory{at1_id} G) ∧ (EQeq G eqid) := by\n'
            + f'  have h0 := (AT_equiv G (conj{at1_id} eqid)).mp h\n'
            + '  rcases eqid\n'
            + '  all_goals\n'
            + '    constructor\n'
            + f'    exact AT_implies G _ h at{at1_id} True.intro\n'
            + "    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0\n"
            + '\n'
            + f'theorem AT{at1_id}_conj (eqid : EQIndex) (G: Type*) [Magma G] : (AssociativeTheory{at1_id} G) ∧ (EQeq G eqid) <-> (ATearly G (conj{at1_id} eqid)) :=\n'
            + '⟨match eqid with\n'
            + ''.join(f'| eq{eqid} => AT{at1_id}_Equation{eqid}_implies G\n' for eqid in all_eqs)
            + f', AT{at1_id}_conj_implied eqid G⟩\n')

to_prove = defaultdict(list)
for at in associative_theories:
    print(at['id'], end='\r')
    for eq_id in all_eqs:
        lcl = at['long']
        goals_at = long_class_to_at[tuple(find_class(at['early'] + [eq_id]))]
        to_prove[at['id']].append((eq_id, goals_at))

for atid in range(1, 457):
    print(atid, end='    \r')
    at1 = atid_to_at[atid]
    with open(f'../associative_theories/Conjunction/Conjunction{atid}.lean', 'w') as f:
        print(preamble, file=f)
        print(lean_conj_map(at1, to_prove[atid]) + '\n', file=f)
        for (id2, at3) in to_prove[atid]:
            print(lean_conj_implies_at(at1, id2, at3) + '\n', file=f)
        print(lean_conj_theorem(at1, to_prove[atid]), file=f)

contents = ('/- Generated file collecting ConjunctionNN files -/\n\n'
            + ''.join(f'import associative_theories.Conjunction.Conjunction{at["id"]}\n' for at in associative_theories)
            + '''
open ATIndex

theorem AT_conj (atid : ATIndex) (eqid : EQIndex) : ∃ (atid2 : ATIndex), ∀ (G: Type*) [Magma G], (ATearly G atid) ∧ (EQeq G eqid) <-> (ATearly G atid2) :=
match atid with
'''
            + ''.join(f'| at{at["id"]} => ⟨_, AT{at["id"]}_conj eqid⟩\n' for at in associative_theories))

with open(f'../associative_theories/Conjunction.lean', 'w') as f:
    print(contents, file=f)

