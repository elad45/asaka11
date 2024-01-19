from pysmt.shortcuts import *
from collections import defaultdict
import sys


def conflicts_handler(content, package_name, var_map, solver):
    for i in range(len(content)):
        if "Conflicts" in content[i]:
            conflicts_line = content[i]
            break
    else:
        return

    conflicts_line = conflicts_line.replace('Conflicts:', '').strip()
    conflicts_arr = [conflict.strip() for conflict in conflicts_line.split(',')]
    for conflict in conflicts_arr:
        var_map[conflict] = Symbol(conflict, BOOL)
        solver.add_assertion(Or(Not(var_map[package_name]), Not(var_map[conflict])))


def make_and_expression(expressions):
    if len(expressions) == 0:
        return None
    if len(expressions) == 1:
        return expressions[0]
    else:
        return And(*expressions)


def make_or_expression(vars_arr):
    if len(vars_arr) == 0:
        return None
    if len(vars_arr) == 1:
        return vars_arr[0]
    else:
        return Or(*vars_arr)


def prepare_asserts(depends_arr, var_map):
    and_expression = []
    for d in depends_arr:
        vars_arr = []
        for names in d.split('|'):
            names.strip()
            var_map[names] = Symbol(names, BOOL)
            vars_arr.append(Symbol(names, BOOL))
        or_expression = make_or_expression(vars_arr)
        and_expression.append(or_expression)
    and_expression = make_and_expression(and_expression)
    return and_expression


def depends_handler(content, package_name, var_map, solver):
    for i in range(len(content)):
        if "Depends" in content[i]:
            depends_line = content[i].replace('Depends:', '').strip()
            depends_arr = [dep.strip() for dep in depends_line.split(',')]
            asserts = prepare_asserts(depends_arr, var_map)
            solver.add_assertion(Or(Not(var_map[package_name]), asserts))

def process_package_data(block, var_map, solver):
    content = block.split('\n')
    package_name = content[0].replace('Package:', '').strip()
    if var_map.get(package_name) is None:
        var_map[package_name] = Symbol(package_name, BOOL)
    depends_handler(content, package_name, var_map, solver)
    conflicts_handler(content, package_name, var_map, solver)


"""
    if len(content) > 1 and "Depends" in content[1]:
        depends_line = content[1].replace('Depends:', '').strip()
        depends_arr = [dep.strip() for dep in depends_line.split(',')]
        asserts = prepare_asserts(depends_arr, var_map, solver)
        solver.add_assertion(Or(Not(var_map[package_name]), asserts))
"""


def process_packages(blocks_arr, var_map, solver):
    for block in blocks_arr:
        process_package_data(block, var_map, solver)


def install_assert(install_names, var_map, solver):

    for name in install_names:
        name=name.strip()
        var_map[name] = Symbol(name, BOOL)
        solver.add_assertion(Symbol(name, BOOL))


def install_to_names(install_block):
    install_names = [pack.strip() for pack in install_block.replace('Install:', '').split(',')]
    return install_names


def parse_input(filename):
    blocks_arr = []
    with open(filename, 'r') as f:
        content = f.read()

    for line in content.split('\n\n'):
        blocks_arr.append(line.strip())
    install_block = blocks_arr[-1]
    blocks_arr = blocks_arr[:-1]
    install_names = install_to_names(install_block)
    return [blocks_arr, install_names]

def find_k_plans(k,var_map,solver):
    plans = []
    for _ in range(k):
        result = solver.check_sat()
        if not result:
            print(f"There are not enough plans for k={k} ")
            return
        current_plan = []
        new_vars = []
        for var in var_map.values():
            if solver.get_value(var).is_true():
                new_vars.append(var)
                current_plan.append(var)
            else:
                new_vars.append(Not(var))
        solver.add_assertion(Not(And(new_vars)))
        plans.append(current_plan)
    print(f"There are at least {k} different plans to solve:\n")
    for i, plan in enumerate(plans, start=1):
        print(f"Plan {i}: {plan}")

if __name__ == "__main__":
    var_map = defaultdict()
    solver = Solver(name="z3")
    # blocks_arr is all the blocks except for the installation, install_names is the last line we want to install
    blocks_arr, install_names = parse_input(sys.argv[1])

    # adds install_names to assert
    install_assert(install_names, var_map, solver)

    process_packages(blocks_arr, var_map, solver)
    k = int(sys.argv[2])
    find_k_plans(k,var_map,solver)
