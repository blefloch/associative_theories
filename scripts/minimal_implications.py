import json
import networkx as nx

with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
with open("../data/eq_to_long_class.json", 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}

def one_conjecture(id1, id2):
    return f"theorem Equation{id1}_4512_implies_Equation{id2} (G : Type*) [Magma G]\n    (eq{id1} : Equation{id1} G) (eq4512 : Equation4512 G) : Equation{id2} G := sorry\n"

def conjecture_preamble():
    preamble = ""
    preamble += "import equational_theories.FactsSyntax\n"
    preamble += "import equational_theories.Equations.All\n"
    preamble += "\n/- Generated file collecting conjectures about single equations -/\n"
    preamble += "\nnamespace Conjectures\n"
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

implication_proofs = []
for id1, id2 in sorted(set(DG.edges()).difference(DGred.edges())):
    implication_proofs.append(nx.shortest_path(DGred, source=id1, target=id2))

def call_conj(p1, p2):
    return f"Conjectures.Equation{p1}_4512_implies_Equation{p2} G eq{p1} eq4512"
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
    return preamble

with open("../associative_theories/OneImpliDeduced.lean", "w") as f:
    print(oneimplideduced_preamble(), file=f)
    for p in implication_proofs:
        print(one_proof(p), file=f)
