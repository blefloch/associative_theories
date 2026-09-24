import json
import networkx as nx
with open("../data/eq_to_long_class.json", 'r') as f:
    eq_to_long_class = {int(k): v for k, v in json.load(f).items()}
eq_to_long_class[4512] = [1, 4512]
with open("../data/explicitly_proven.json", 'r') as f:
    explicitly_proven = json.load(f)

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
    preamble += "import associative_theories.VampireProvenOne\n\n"
    preamble += "/- Generated file for the single-equation implication graph -/\n\n"
    preamble += "open VampireProven\n\n"
    return preamble

DG = nx.DiGraph()
edge_list = [(id1, id2) for id1, lcl in eq_to_long_class.items()
             for id2 in lcl if len({id1, id2, 4512}) == 3]
DG.add_edges_from(set(edge_list))
DGred = nx.DiGraph()
edge_list = [(premises[0], k)
             for premises, klist in explicitly_proven
             for k in klist
             if len(premises) == 2]
DGred.add_edges_from(set(edge_list))
implication_proofs = []
for id1, id2 in sorted(set(DG.edges()).difference(DGred.edges())):
    implication_proofs.append(nx.shortest_path(DGred, source=id1, target=id2))

with open("../associative_theories/OneImpliDeduced.lean", "w") as f:
    print(oneimplideduced_preamble(), file=f)
    print("theorem Equation4512_implies_Equation1 (G : Type*) [Magma G] (_ : Equation4512 G) : Equation1 G := by rw [Equation1]; intros; rfl\n", file=f)
    for p in implication_proofs:
        print(one_proof(p), file=f)
