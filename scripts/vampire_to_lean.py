#!/usr/bin/env python3
'''
Adapted from the Equational Theories Project file vampire_proofs.py at
https://github.com/teorth/equational_theories/blob/main/equational_theories/Generated/VampireProven/src/vampire_proofs.py

Here we produce theorems like the following:

theorem Equation8_440_4512_implies_Equation11 (G : Type*) [Magma G]
    (h8 : Equation8 G) (h440 : Equation440 G) (h4512 : Equation4512 G) : Equation11 G := sorry
'''

import subprocess
from find_equation_id import Equation
import re

VAMPIRE = "./vampire"

BVARS = "XYZWUVABC"

def format_expr2(shape, rhymes):
    if shape is None:
        return next(rhymes)
    return f"mul({format_expr2(shape[0], rhymes)}, {format_expr2(shape[1], rhymes)})"


def format_eq(eq_id):
    eq = Equation.from_id(eq_id)
    v = ""
    for x in BVARS[:eq.num_vars()]:
        v += f"! [{x}] : "
    rhymes = (BVARS[i] for i in eq.rhyme)
    return (v + format_expr2(eq.lhs_shape, rhymes)
            + " = " + format_expr2(eq.rhs_shape, rhymes))

def encode_problem(assumptions, goal):
    return ("".join(f"fof(h{i}, axiom, {format_eq(i)}).\n" for i in assumptions)
            + f"fof(rhs, conjecture, {format_eq(goal)}).\n")


# Leanify

def natural_sort(l):
    def convert(text):
        return int(text) if text.isdigit() else text.lower()

    def alphanum_key(key):
        return [convert(c) for c in re.split("([0-9]+)", key)]

    return sorted(l, key=alphanum_key)


def leanifyS(statement):
    statement = re.sub("mul", "", statement)
    statement = re.sub(",", " ◇ ", statement)
    statement = re.sub("!=", "≠", statement)
    variables = natural_sort({x for x in re.findall("\\w+", statement) if "sK" not in x})
    variables = f'({" ".join(variables)} : G) ' if variables else ""
    return f"{variables}: {statement}"


def leanifyP(proof):
    sr = re.match(r"superposition (\d+),(\d+)", proof)
    if sr is not None:
        return f"superpose eq{sr[2]} eq{sr[1]}"
    sr = re.match(r"backward demodulation (\d+),(\d+)", proof)
    if sr is not None:
        return f"superpose eq{sr[2]} eq{sr[1]}"
    sr = re.match(r"forward demodulation (\d+),(\d+)", proof)
    if sr is not None:
        return f"superpose eq{sr[2]} eq{sr[1]}"
    raise NotImplementedError(proof)


def leanify(proof, problem):
    assumptions, goal = problem
    assumptions_eq = [Equation.from_id(i) for i in assumptions]
    goal_eq = Equation.from_id(goal)
    used_hypotheses = []
    output_proof = ""
    output_proof += "  by_contra nh\n  simp only [not_forall] at nh\n"
    output_proof += f'  obtain ⟨{", ".join("sK" + str(i) for i in range(goal_eq.num_vars()))}, nh⟩ := nh\n'
    for eqnum, statement, proof in re.findall(r"(\d+)\. ([^[]+) \[([^\]]+)\]", proof):
        # print(eqnum, statement, proof)
        if proof.startswith("X") or proof.startswith("skolemisation"):
            continue
        if proof.startswith("cnf transformation"):
            if "!=" in statement:
                output_proof += f"  have eq{eqnum} {leanifyS(statement)} := mod_symm nh\n"
            else:
                ls = leanifyS(statement)
                i = Equation.from_str(ls.split(":")[-1]).id
                used_hypotheses.append(i)
                output_proof += f"  have eq{eqnum} {ls} := mod_symm (h{i} ..)\n"
            continue
        if statement == "$false":
            sr = re.match(r"subsumption resolution (\d+),(\d+)", proof)
            if sr is not None:
                output_proof += f"  subsumption eq{sr[1]} eq{sr[2]}\n\n"
                continue
            sr = re.match(r"trivial inequality removal (\d+)", proof)
            if sr is not None:
                output_proof += f"  subsumption eq{sr[1]} rfl\n\n"
                continue
            sr = re.match(r"equality resolution (\d+)", proof)
            if sr is not None:
                output_proof += f"  subsumption eq{sr[1]} rfl\n\n"
                continue
            print(output_proof)
            raise NotImplementedError(proof)
        else:
            output_proof += f"  have eq{eqnum} {leanifyS(statement)} := {leanifyP(proof)} -- {proof}\n"
    return (
        'theorem Equation'
        + "_".join(str(i) for i in assumptions)
        + f'_implies_Equation{goal} '
        + f'(G : Type*) [Magma G]\n    '
        + ' '.join((f'(h{i}' if i in used_hypotheses else '(_')
                   + f' : Equation{i} G)'
                   for i in assumptions)
        + f' : Equation{goal} G := by\n'
        + output_proof
    )

def trivial_lean_proof(assumptions):
    '''Proof that anything implies Equation1'''
    return (
        'theorem Equation'
        + "_".join(str(i) for i in assumptions)
        + f'_implies_Equation1 '
        + f'(G : Type*) [Magma G]\n    '
        + ' '.join(f'(_ : Equation{i} G)' for i in assumptions)
        + f' : Equation1 G := by\n'
        + "  intro x\n  rfl\n"
    )



# Main function

def prove_lean(assumptions, goal):
    if goal == 1:
        return trivial_lean_proof(assumptions)
    problem = (assumptions, goal)
    pr = encode_problem(assumptions, goal)
    try:
        out = subprocess.check_output(
            [VAMPIRE, "--statistics", "none", "--proof_extra", "free", "-t", "10", "/proc/self/fd/0"],
            input=pr.encode(),
        ).decode()
    except subprocess.CalledProcessError:
        print("================================")
        print(problem)
        print("================================")
        print(pr)
        print("================================")
        return ""
    lean_proof = leanify(out, problem)
    return lean_proof
