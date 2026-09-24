from vampire_to_lean import prove_lean
import json
with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)
with open("../data/explicitly_proven.json", 'r') as f:
    explicitly_proven = json.load(f)

##### Generate Lean files

def vampire_proven_preamble(how_many = "single", facts = False, superposition = False):
    preamble = ""
    if facts: preamble += "import equational_theories.FactsSyntax\n"
    if superposition:
        preamble += ("import equational_theories.Superposition\n"
                     "import Mathlib.Tactic.TypeStar\n"
                     "import Mathlib.Tactic.ByContra\n")
    preamble += "import equational_theories.Equations.All\n"
    preamble += f"\n/- Generated file collecting results about {how_many} equations -/\n"
    preamble += "\nnamespace VampireProven\n"
    return preamble
def vampire_proven_postamble():
    return "\nend VampireProven\n"

with open("../associative_theories/VampireProvenEquiv.lean", "w") as f:
    print(vampire_proven_preamble(superposition = True), file=f)
    for cl in eq_classes:
        if len(cl) > 1:
            print(f"\n/- Equivalence of {cl} -/", file=f)
            for i in range(len(cl)):
                problem = ([cl[i - 1], 4512], cl[i])
                print(problem, end="     \r")
                proof = prove_lean(*problem)
                print(proof, end="", file=f)
    print(vampire_proven_postamble(), file=f)

with open("../associative_theories/VampireProvenOne.lean", "w") as f:
    print(vampire_proven_preamble(superposition = True), file=f)
    for premises, kset in explicitly_proven:
        if len(premises) == 2:
            id1 = premises[0]
            for k in sorted(kset):
                print((premises, k), end="     \r")
                proof = prove_lean(premises, k)
                print(proof, end="", file=f)
    print(vampire_proven_postamble(), file=f)


with open("../associative_theories/VampireProvenTwo.lean", "w") as f:
    print(vampire_proven_preamble("pairs of", superposition = True), file=f)
    for premises, kset in explicitly_proven:
        if len(premises) > 2:
            for k in sorted(kset):
                print((premises, k), end="     \r")
                proof = prove_lean(premises, k)
                print(proof, end="", file=f)
    print(vampire_proven_postamble(), file=f)
