import json
from collections import defaultdict

with open('../data/associative_equation_classes.json', 'r') as f:
    eq_classes = json.load(f)
reps = [min(cl) for cl in eq_classes]
with open('../data/long_classes.json', 'r') as f:
    long_classes = json.load(f)
with open('../data/eq_to_long_class.json', 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}
eq_to_long_class[4512] = [1, 4512]
with open('../data/associative_theories.json', 'r') as f:
    associative_theories = json.load(f)
long_to_at = {}
for at in associative_theories:
    long_to_at[tuple(sorted(at['long']))] = at
with open('../data/explicitly_proven.json', 'r') as f:
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

def eq_to_at(eqid):
    return long_to_at[tuple(find_class((eqid,)))]

for eq_id in reps:
    available_theorems[eq_id, 4512] = eq_to_long_class[eq_id]

preamble = \
'''/- Generated implication graph of associative theories -/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.AssociativeTheoriesIndex
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.VampireProvenOne
import associative_theories.VampireProvenTwo
import associative_theories.OneImpliDeduced
import associative_theories.EarlyLongEquiv

open ATIndex
open VampireProven

'''

#####################
def lean_eq_list(eqs, prefix='h'):
    if len(eqs) > 1:
        return '⟨' + ', '.join(map(lambda x: prefix + str(x), eqs)) + '⟩'
    return prefix + str(eqs[0])

def lean_implications(at1):
    id1 = at1['id']
    lcl1s = set(at1['long'])
    return (f'def AT{id1}_impliesQ : ATIndex -> Prop\n'
            + ''.join(f'| at{at2["id"]} => {lcl1s.issuperset(at2["early"])}\n' for at2 in associative_theories)
            + '\n'
            + f'theorem AT{id1}_implies (atid: ATIndex) (hh: AT{id1}_impliesQ atid) (G: Type*) [Magma G] (h: AssociativeTheory{id1} G) : ATearly atid G := by\n'
            + '  obtain ' + lean_eq_list(at1['long']) + f' := (AT_equiv at{id1} G).mp h\n'
            + '  rcases atid <;> try exact False.elim hh\n'
            + ''.join('  exact ' + lean_eq_list(at2['early']) + '\n'
                      for at2 in associative_theories
                      if lcl1s.issuperset(at2["early"])))

assert 456 == 24 * 19

with open('../associative_theories/ImplicationsAT.lean', 'w') as f:
    print('/- Generated implication graph of associative theories -/\n\n'
          + ''.join(f'import associative_theories.ImplicationsAT.ImplicationsAT{k}\n' for k in range(1, 25))
          + '\nopen ATIndex\n\n'
          + 'def AT_impliesQ : ATIndex -> ATIndex -> Prop\n'
          + ''.join(f'| at{i} => AT{i}_impliesQ\n' for i in range(1, 457))
          + '\n'
          + 'theorem AT_implies (atid: ATIndex) (atid2: ATIndex) (hh: AT_impliesQ atid atid2) :\n'
          + '  ∀(G: Type*) [Magma G], (ATearly atid G) -> (ATearly atid2 G) :=\n'
          + 'match atid with\n'
          + ''.join(f'| at{i} => AT{i}_implies atid2 hh\n' for i in range(1, 457))
          + '\n'
          + "theorem AT_implies' (atid: ATIndex) (G: Type*) [Magma G] (h: ATearly atid G)\n"
          + '  (atid2: ATIndex) (hh: AT_impliesQ atid atid2) : (ATearly atid2 G) :=\n'
          + '  AT_implies atid atid2 hh G h\n',
          file=f)

for k in range(1, 25):
    with open(f'../associative_theories/ImplicationsAT/ImplicationsAT{k}.lean', 'w') as f:
        print(preamble, file=f)
        for at1 in associative_theories:
            if 1 + ((at1['id'] - 1) // 19) == k:
                print(lean_implications(at1), file=f)
