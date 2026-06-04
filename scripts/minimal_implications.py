import json
import networkx as nx

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
with open("../data/eq_to_long_class.json", 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}

def one_conjecture(id1, id2):
    return f"@[equational_result]\nconjecture Equation{id1}_implies_Equation{id2} (G : Type*) [Magma G] (_ : Equation{id1} G) : Equation{id2} G"

def conjecture_preamble():
    preamble = ""
    preamble += "import equational_theories.FactsSyntax\n"
    preamble += "import equational_theories.EquationalResult\n"
    preamble += "import equational_theories.Equations.All\n"
    preamble += "import Mathlib.Data.Set.Finite.Basic\n\n"
    preamble += "/- Generated file collecting conjectures about single equations -/"
    preamble += "\n\nnamespace Conjectures\n"
    return preamble
def conjecture_postamble():
    return "\nend Conjectures\n"

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
             for id2 in lcl if id1 != id2 and id2 != 4512]
DG.add_edges_from(set(edge_list))
DGred = nx.transitive_reduction(DG)

with open("../associative_theories/ConjecturesOneImpli.lean", "w") as f:
    print(conjecture_preamble(), file=f)
    for id1, id2 in sorted(DGred.edges()):
        print(one_conjecture(id1, id2), file=f)
    print(conjecture_postamble(), file=f)



