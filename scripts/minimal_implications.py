import json
with open("../data/associative_equation_classes.json", 'r') as f:
    eq_classes = json.load(f)

def one_conjecture(id1, id2):
    return f"@[equational_result]\nconjecture Equation{id1}_implies_Equation{id2} (G : Type*) [Magma G] (_ : Equation{id1} G) : Equation{id2} G"

with open("../associative_theories/ConjecturesOneEquiv.lean", "w") as f:
    print("import equational_theories.FactsSyntax", file=f)
    print("import equational_theories.EquationalResult", file=f)
    print("import equational_theories.Equations.All", file=f)
    print("import Mathlib.Data.Set.Finite.Basic", file=f)
    print("\n/- Generated file collecting conjectures about single equations -/", file=f)
    print("\nnamespace Conjectures\n", file=f)
    for cl in eq_classes:
        if len(cl) > 1:
            print(f"\n/- Equivalence of {cl} -/", file=f)
            for i in range(len(cl)):
                print(one_conjecture(cl[i - 1], cl[i]), file=f)
    print("\nend Conjectures\n", file=f)
