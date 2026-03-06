from find_equation_id import Equation, shape_order
import itertools
import subprocess
import re

PIPE = subprocess.PIPE

MACE4 = "./mace4"
PROVER9 = "./prover9"
ISOFILTER = "./isofilter"
MAX_SECONDS = 1

### Helpers about processes
def set_max_seconds(max_seconds):
    global MAX_SECONDS
    MAX_SECONDS = max_seconds

def run_one(*popenargs, input=None, timeout=None, check=False, **kwargs):
    # todo: why not just subprocess.run?
    with subprocess.Popen(*popenargs, text=True, stdin=PIPE, stdout=PIPE, stderr=PIPE, **kwargs) as process:
        try:
            stdout, stderr = process.communicate(input, timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            process.kill()
            process.wait()
            raise
        except:
            process.kill()
            raise
        retcode = process.poll()
        if check and retcode:
            raise subprocess.CalledProcessError(retcode, process.args,
                                                output=stdout, stderr=stderr)
    return subprocess.CompletedProcess(process.args, retcode, stdout, stderr)

### Helpers about equations
def to_list(eq):
    if isinstance(eq, Equation):
        return [eq]
    try:
        result = list(iter(eq))
    except TypeError:
        result = [eq]
    return result

def to_eq(eq):
    if isinstance(eq, Equation):
        return eq
    if isinstance(eq, str):
        return Equation.from_str(eq)
    try:
        eq_int = int(eq)
    except:
        eq_int = 0
    if eq_int > 0:
        return Equation.from_id(eq_int)
    elif eq_int == 0:
        raise ValueError("eq cannot be 0")
    return eq

def eq_str(eq):
    return str(to_eq(eq)).replace("◇", "*")

### Misc

def all_magmas(n):
    return (tuple(m[n*i:n*i+n] for i in range(n)) for m in itertools.product(range(n), repeat = n ** 2))

def evaluate_with_magma(shape, leaves, m):
    """Here leaves is the actual magma elements to be inserted!"""
    if shape is None:
        if len(leaves) == 1:
            return leaves[0]
        raise ValueError(leaves)
    left, right = shape
    num = shape_order(left) + 1
    return m[leaves[0] if num == 1 else evaluate_with_magma(left, leaves[:num], m)][
             leaves[-1] if num == len(leaves) - 1 else evaluate_with_magma(right, leaves[num:], m)]

def test_eq_with_magma(eq, m):
    eqq = to_eq(eq)
    n = len(m)
    for xyz in itertools.product(range(n), repeat = max(eqq.rhyme) + 1):
        leaves = tuple(xyz[i] for i in eqq.rhyme)
        num = shape_order(eqq.lhs_shape) + 1
        if evaluate_with_magma(eqq.lhs_shape, leaves[:num], m) != evaluate_with_magma(eqq.rhs_shape, leaves[num:], m):
            return False
    return True

def num_leaves(shape):
    if shape is None:
        return 1
    left, right = shape
    return num_leaves(left) + num_leaves(right)

### Constructing tasks
def _models_task(equation1, equation2, extra0, extra1, extra2, max_models, max_seconds):
    return f'''
assign(selection_order, 2).
assign(selection_measure, 1).
assign(max_models, {max_models}).
assign(max_seconds, {max_seconds}).
assign(iterate_up_to, 100).
{extra0}
formulas(sos).
{extra1}
{'.'.join(equation1) + '.' if equation1 else ''}
end_of_list.
formulas(goals).
{extra2}
{'&'.join(equation2) + '.' if equation2 else ''}
end_of_list.'''

def _prove_task(equation1, equation2, extra0, extra1, extra2, max_seconds):
    return f'''
assign(sos_limit, 2000).
assign(max_weight, 1000).
assign(max_seconds, {max_seconds}).
{extra0}
formulas(sos).
{extra1}
{'.'.join(equation1) + '.'  if equation1 else ''}
end_of_list.
formulas(goals).
{extra2}
{'.'.join(equation2) + '.' if equation2 else ''}
end_of_list.'''

### models, prove, models_or_prove
def models(eq1, eq2, *, max_models=1, max_seconds=0, check_timeout=False, extra0='', extra1='', extra2='', debug=False, isofilter=True, timeout=None):
    if max_seconds == 0:
        max_seconds = MAX_SECONDS
    eq1_list = to_list(eq1)
    eq2_list = to_list(eq2)
    equation1 = [eq_str(eq) for eq in eq1_list]
    equation2 = [eq_str(eq) for eq in eq2_list]
    task = _models_task(equation1, equation2, extra0, extra1, extra2, max_models, max_seconds)
    if debug:
        print(task)
    try:
        maceproc = run_one(MACE4, input=task, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        if check_timeout:
            return False
        return False
    if check_timeout and (maceproc.returncode in [1, 4, 5, 7]):
        #print(f"timeout for Equation {eq.id}: {eq}")
        return False
    mace4models = '\n'.join(re.findall('(?s)interpretation.*?\\]\\)\\.', maceproc.stdout))
    if isofilter:
        try:
            isoproc = run_one(ISOFILTER, input=mace4models, timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            if check_timeout:
                return False
            return False
        interpretations = '\n'.join(re.findall('(?s)interpretation.*?\\]\\)\\.', isoproc.stdout))
    else:
        interpretations = mace4models
    return [[[int(s) for s in row.split(",")]
             for row in re.split(",\n\\s*", model)]
            for model in re.findall("\\d+(?:,\\s?\\d+)+(?:,\n\\s*\\d+(?:,\\s?\\d+)+)+", interpretations)]

def prove(eq1, eq2, *, max_seconds=0, check_timeout=False, extra0='', extra1='', extra2='', timeout=None, full_output=False):
    if max_seconds == 0:
        max_seconds = MAX_SECONDS
    eq1_list = to_list(eq1)
    eq2_list = to_list(eq2)
    equation1 = [eq_str(eq) for eq in eq1_list]
    equation2 = [eq_str(eq) for eq in eq2_list]
    task = _prove_task(equation1, equation2, extra0, extra1, extra2, max_seconds)
    try:
        proverproc = run_one(PROVER9, input=task, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        if check_timeout:
            return False
        return False
    if proverproc.returncode == 0:
        return proverproc.stdout if full_output else True
    if check_timeout and proverproc.returncode == 4:
        #print(f"timeout for Equation {eq1.id}->{eq2.id}: {eq1} -> {eq2}")
        return False
    return False
