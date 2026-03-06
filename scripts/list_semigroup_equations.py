from find_equation_id import Equation, all_eqs

eqs_found = []
for order in range(5):
    for eq in all_eqs(order):
        semigroup_eq = str(eq).replace("(", "").replace(")", "")
        lhs, rhs = semigroup_eq.split(" = ")
        if lhs != rhs:
            eqs_found.append(semigroup_eq)
for eq_str in dict.fromkeys(eqs_found):
    print(eq_str)
