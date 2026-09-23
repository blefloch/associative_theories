from vampire_proofs_conj import prove_lean
import json
with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
with open("../data/explicitly_proven.json", 'r') as f:
    explicitly_proven = json.load(f)

##### Generate Lean files

def conjecture_preamble(how_many = "single", facts = False, superposition = False):
    preamble = ""
    if facts: preamble += "import equational_theories.FactsSyntax\n"
    if superposition:
        preamble += ("import equational_theories.Superposition\n"
                     "import Mathlib.Tactic.TypeStar\n"
                     "import Mathlib.Tactic.ByContra\n")
    preamble += "import equational_theories.Equations.All\n"
    preamble += f"\n/- Generated file collecting conjectures about {how_many} equations -/\n"
    preamble += "\nnamespace Conjectures\n"
    return preamble
def conjecture_postamble():
    return "\nend Conjectures\n"

#def one_conjecture(id1, id2):
#    return f"theorem Equation{id1}_4512_implies_Equation{id2} (G : Type*) [Magma G]\n    (eq{id1} : Equation{id1} G) (eq4512 : Equation4512 G) : Equation{id2} G := sorry\n"
#
#def multi_conjecture(ids, id2):
#    return (f"theorem Equation{'_'.join(map(str, ids))}_implies_Equation{id2} (G : Type*) [Magma G]\n    "
#            + " ".join(f"(h{eq_id} : Equation{eq_id} G)" for eq_id in ids)
#            + f" : Equation{id2} G := sorry\n")

with open("../associative_theories/ConjecturesOneEquiv.lean", "w") as f:
    print(conjecture_preamble(superposition = True), file=f)
    for cl in eq_classes:
        if len(cl) > 1:
            print(f"\n/- Equivalence of {cl} -/", file=f)
            for i in range(len(cl)):
                #print(one_conjecture(cl[i - 1], cl[i]), file=f)
                problem = ([cl[i - 1], 4512], cl[i])
                print(problem, end="     \r")
                proof = prove_lean(*problem)
                print(proof, end="", file=f)
    print(conjecture_postamble(), file=f)

with open("../associative_theories/ConjecturesOneImpli.lean", "w") as f:
    print(conjecture_preamble(superposition = True), file=f)
    for premises, kset in explicitly_proven:
        if len(premises) == 2:
            id1 = premises[0]
            for k in sorted(kset):
                print((premises, k), end="     \r")
                proof = prove_lean(premises, k)
                print(proof, end="", file=f)
    print(conjecture_postamble(), file=f)


with open("../associative_theories/ConjecturesTwo.lean", "w") as f:
    print(conjecture_preamble("pairs of", superposition = True), file=f)
    for premises, kset in explicitly_proven:
        if len(premises) > 2:
            for k in sorted(kset):
                print((premises, k), end="     \r")
                proof = prove_lean(premises, k)
                print(proof, end="", file=f)
    print(conjecture_postamble(), file=f)



