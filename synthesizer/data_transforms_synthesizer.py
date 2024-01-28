import csv
import datetime
import glob
import hashlib
import json
import multiprocessing
import multiprocessing.dummy  # So it uses threads, not processes
import os.path
import sys
import tempfile
import time
from enum import Enum
from typing import Any

from synthesizer.to_cvc5 import get_cvc5_query, run_cvc5_command
from synthesizer.to_rosette import get_rosette_query, run_racket_command
from synthesizer.to_synthesis import get_synthesis_indices, get_synthesis_keys, get_synthesis_values
from synthesizer.util import human_time

# Where each subproblem thread saves its positive solution
valid_sat_subproblem_solutions: list[dict[str, Any], ...] = []
# Where the complete problem threads save the most recent timeout or unsat solution
timeout_or_unsat_complete_problem_solution: dict[str, Any] | None = None

SynthesisSolver = Enum('SynthesisSolver', ['CVC5', 'Rosette'])


def get_timestamp() -> str:
    """
    Get a timestamp in the format YYYYMMDDHHMMSS
    :return: timestamp string
    """
    now = datetime.datetime.now()
    timestamp = now.strftime("%Y%m%d%H%M%S")
    return timestamp


def my_hash(s: str) -> int:
    return abs(int(hashlib.sha512(s.encode('utf-8')).hexdigest(), 16) % 10 ** 12)


def get_synthesis_filename(depth: int, func_name: str, instance_name: str, keys: list[str],
                           values: list[str], extenstion: str = 'txt') -> str:
    timestamp = get_timestamp()

    return (f'{instance_name}{"" if func_name[0] == "_" else "_"}'
            f'{func_name}_{my_hash(str(keys) + str(values))}'
            f'_{str(depth) + "_" if depth is not None else ""}'
            f'{timestamp}.{extenstion}')


def preprocess(synt_decl: dict[str:Any], use_metadata: bool = True) -> tuple[dict[str:Any], str]:
    """
    Remove whole constraints (i.e., I/O pairs), or remove one or more inputs if they should not be used for synthesis.
    Removes constraints if
    - the output is None.
    Removes inputs if
    - It is the same in every constraint.
    - Is undefined in at least one constraint.

    IDEA: Remove from dictionary key-pairs that re the same across all constraints?
    :param synt_decl: synthesis single function declaration, as read from the json
    :param use_metadata: bool indicating whether metadata should be removed from the inputs
    :return: (synt_decls, comments): the new function declaration, in the same format as inputted,
    and a comment string describing the changes that were made.
    """
    comment = ''
    # Remove any constraint whose output is None
    constraints = synt_decl['constraints']
    ctrs_to_remove = []
    for i, c in enumerate(constraints):
        if c['output'] is None:
            ctrs_to_remove.append(i)
    if len(ctrs_to_remove) > 0:
        comment += f'Removing constraints {ctrs_to_remove} because output is Null.\n'
    for i in sorted(ctrs_to_remove, reverse=True):
        synt_decl['constraints'].pop(i)

    # Remove inputs which are always the same
    # constraints = synt_decl['constraints']
    # in_idx_to_remove = []
    # for i in range(len(constraints[0]['inputs'])):
    #     if all(ctr['inputs'][i] == constraints[0]['inputs'][i] for ctr in constraints):
    #         in_idx_to_remove.append(i)
    # for i in sorted(in_idx_to_remove, reverse=True):
    #     for ctr in synt_decl['constraints']:
    #         ctr['inputs'].pop(i)
    # if len(in_idx_to_remove) > 0:
    #     comment += f'Removing inputs {in_idx_to_remove} because always the same.\n'

    # Remove inputs which are undefined in some constraint
    constraints = synt_decl['constraints']
    in_idx_to_remove = []
    for i in range(len(constraints[0]['inputs'])):
        if any(ctr['inputs'][i] is None for ctr in constraints):
            in_idx_to_remove.append(i)
    if len(in_idx_to_remove) > 0:
        comment += f'Removing inputs {in_idx_to_remove} because sometimes Null.\n'
    for i in sorted(in_idx_to_remove, reverse=True):
        for ctr in synt_decl['constraints']:
            ctr['inputs'].pop(i)

    if not use_metadata:
        # Remove "metadata" fields from inputs
        constraints = synt_decl['constraints']
        in_idx_with_metadata = []
        for i in range(len(constraints[0]['inputs'])):
            if all(isinstance(ctr['inputs'][i], dict) and  # input is a dict
                   any('metadata' in k for k in [s.lower() for s in ctr['inputs'][i].keys()])  # there is metadata in it
                   for ctr in constraints):  # in all constraints
                in_idx_with_metadata.append(i)
        for i in sorted(in_idx_with_metadata, reverse=True):
            for ctr in synt_decl['constraints']:
                metadata_keys = list(filter(lambda s: 'metadata' in s.lower(), ctr['inputs'][i].keys()))
                for k in metadata_keys:
                    del ctr['inputs'][i][k]
                comment += f'Removing fields {metadata_keys} from all inputs because they are metadata.\n'

    return synt_decl, comment


def synthesize_data_transforms(
        instance_name: str, synt_decls: list[dict[str:Any]],
        solver: SynthesisSolver, synthesis_timeout: int,
        use_metadata: bool = True) \
        -> list[dict[str:Any]]:
    """
    Given synthesis function declarations, with a name and a list of constraints,
    synthesize a JSONPath expression for each undefined function.
    :param instance_name: The instance name, which will be used to name auxiliary
       synthesis file and solution file.
    :param synt_decls: Input read from the json file.
    :param solver: The synthesis solver to use.
    :param synthesis_timeout: Max synthesis time in seconds.
    :param use_metadata: Whether metadata should be used as input to the synthesis
    :return solution dictionary
    """
    global valid_sat_subproblem_solutions
    global timeout_or_unsat_complete_problem_solution
    solutions_dir = "data_synthesis_solutions/"
    all_solutions = []

    # The synthesis of each data transform is solved sequencially
    for synt_decl in sorted(synt_decls, key=lambda decl: decl['name']):

        # String values collected from the instances, because Rosette's strings are not solvable types.
        keys = sorted(get_synthesis_keys(synt_decl))
        indices = get_synthesis_indices(synt_decl)
        values = sorted(get_synthesis_values(synt_decl), key=lambda v: (isinstance(v, str), v))

        num_processes = multiprocessing.cpu_count() // 2

        # If there are many keys and/or values, and we have more than one CPU,
        # we split the keys and values into subsets and make smaller subproblems.
        if (len(keys) > 15 or len(values) > 15) and num_processes > 1:
            # We split it, so we have (approximately) as many subproblems
            # per depth as the computer has CPUs.
            # Total_keys_vals = len(keys) + len(values)
            # list_size = max(1, int(total_keys_vals / max(1, 4*num_processes - 1)))
            # Fixed listsize:
            list_size = 16
            keys_sublists = [keys[i:i + list_size] for i in range(0, len(keys), list_size)]
            values_sublists = [values[i:i + list_size] for i in range(0, len(values), list_size)]

            # Some subproblems have only keys, others have only values
            keys_values = [(k, []) for k in keys_sublists] + \
                          [([], v) for v in values_sublists]
        else:
            keys_values = []  # no subproblems otherwise
        # Define all subproblems
        if solver == SynthesisSolver.Rosette:
            depths = range(2, 6)
        elif solver == SynthesisSolver.CVC5:
            depths = (None,)
        else:
            raise NotImplementedError(f'Synthesis solver {SynthesisSolver} not implemented.')
        subproblems_args = [
            (synt_decl, indices, keys, values, depth, instance_name,
             solver, synthesis_timeout, use_metadata, True)
            for depth in depths
            for keys, values in keys_values]

        if solver == SynthesisSolver.Rosette:
            depths = range(2, 6)
        elif solver == SynthesisSolver.CVC5:
            depths = (None,)
        else:
            raise NotImplementedError(f'Synthesis solver {SynthesisSolver} not implemented.')
        # Define the complete problem
        complete_problem_args = [
            (synt_decl, indices, keys, values, depth, instance_name,
             solver, synthesis_timeout, use_metadata, False)
            for depth in depths]

        valid_sat_subproblem_solutions = []  # clear list from previous runs
        timeout_or_unsat_complete_problem_solution = None  # clear list from previous runs

        # Start processes solving subproblems
        with multiprocessing.dummy.Pool(processes=num_processes - 1) as subproblems_pool:
            async_result_subproblems = subproblems_pool.starmap_async(
                write_and_solve_synthesis_problem, subproblems_args)

            with multiprocessing.dummy.Pool(processes=1) as main_problem_pool:
                async_result_complete_problem = main_problem_pool.starmap_async(
                    write_and_solve_synthesis_problem, complete_problem_args)

                start_time = time.perf_counter()

                # cycle that watches all threads:
                while time.perf_counter() - start_time < synthesis_timeout:
                    time.sleep(0.1)  # Check every 0.1 secs
                    # valid_sat_subproblem_solutions is updated by the
                    # subproblem threads to include only SAT solutions
                    if len(valid_sat_subproblem_solutions) > 0:
                        # One of the subproblems returned SAT
                        # add instance name to solutions
                        for sol in valid_sat_subproblem_solutions:
                            sol['instance'] = instance_name
                        all_solutions.extend(valid_sat_subproblem_solutions)
                        break  # stop watching threads

                    elif async_result_complete_problem.ready():  # Even if it times out, it should be caught here.
                        # Complete problem finished (either successfully or not)
                        # add instance name to solutions
                        complete_problem_solutions = async_result_complete_problem.get()
                        for sol in complete_problem_solutions:
                            sol['instance'] = instance_name
                        all_solutions.extend(complete_problem_solutions)
                        break  # stop watching threads

                # Stop all threads
                subproblems_pool.close()
                subproblems_pool.terminate()
                main_problem_pool.close()
                main_problem_pool.terminate()

                if len(all_solutions) == 0:
                    assert time.perf_counter() - start_time > synthesis_timeout
                    if timeout_or_unsat_complete_problem_solution is not None:
                        timeout_or_unsat_complete_problem_solution['instance'] = instance_name
                    all_solutions.append(timeout_or_unsat_complete_problem_solution)

                # Write all solutions to solutions file, even before it has
                # computed solutions for all functions.
                solution_filename = f'{instance_name}_{solver.name}.json'
                if not os.path.isdir(solutions_dir):
                    os.makedirs(solutions_dir)
                with open(os.path.join(solutions_dir, solution_filename), 'w') as sol_file:
                    json.dump(all_solutions, sol_file, indent=2)

        subproblems_pool.close()
        subproblems_pool.terminate()
        main_problem_pool.close()
        main_problem_pool.terminate()

    return all_solutions


def write_and_solve_synthesis_problem(synt_decl, indices: list[int], keys: list[str], values: list[str],
                                      depth: int | None, instance_name: str, synthesis_solver: SynthesisSolver,
                                      synthesis_timeout: int, use_metadata: bool, is_subproblem: bool):
    """
    Auxiliary function that, given information about a synthesis instance,
    writes a synthesis query in synthesis_solver language to a file and solves it.
    :param synt_decl: The synthesis problem, read from the instance file.
    :param indices: The constant values that should be considered for SyntInt.
    :param keys: The strings that should be considered for SyntK.
    :param values: The strings that should be considered for SyntVal.
    :param depth: The maximum depth of the synthesized program. Not used for CVC5.
    :param instance_name: The instance name.
    :param synthesis_solver: The synthesis solver to use.
    :param synthesis_timeout: Synthesis timeout in seconds
    :param use_metadata: Whether metadata fields should be used for synthesis.
    :param is_subproblem: Whether this is a subproblem for a bigger synthesis problem.
    :return:
    """
    global valid_sat_subproblem_solutions
    global timeout_or_unsat_complete_problem_solution
    synt_decl, comment = preprocess(synt_decl, use_metadata)
    if synthesis_solver == SynthesisSolver.Rosette:
        assert depth is not None
        synthesis_text = get_rosette_query(depth, indices, keys, synt_decl, values)
        extension = 'rkt'
    elif synthesis_solver == SynthesisSolver.CVC5:
        assert depth is None
        synthesis_text = get_cvc5_query(indices, keys, synt_decl, values)
        extension = 'sl'
    else:
        raise NotImplementedError(f'Synthesis solver {SynthesisSolver} not implemented.')
    func_name = synt_decl['name']
    suffix = get_synthesis_filename(depth, func_name, instance_name, keys, values, extension)
    with tempfile.NamedTemporaryFile('w', suffix=suffix, delete=False) as f:
        f.write(synthesis_text)
        synthesis_filename = f.name
        # print(f'{synthesis_solver.name} file written to {synthesis_filename}')
    # Uncomment to DEBUG sl file
    with open(f'synth.{extension}', 'w') as f:
        f.write(synthesis_text)
        # print(f'{synthesis_solver.name} file written to synth.{extension}')
    start_call_time = time.perf_counter()
    if synthesis_solver == SynthesisSolver.CVC5:
        synthesis_ans_out = run_cvc5_command(synthesis_filename, synthesis_timeout)
    elif synthesis_solver == SynthesisSolver.Rosette:
        synthesis_ans_out = run_racket_command(synthesis_filename, synthesis_timeout)
    else:
        raise NotImplementedError(f'Synthesis solver {SynthesisSolver} not implemented.')
    elapsed = time.perf_counter() - start_call_time
    solution = {'name': func_name,
                'solution': synthesis_ans_out,
                'solve time': elapsed,
                'solve time (h)': human_time(elapsed),
                'keys': keys,
                'values': values,
                'depth': depth,
                'solver': synthesis_solver.name,
                'is subproblem': is_subproblem,
                'comment': comment}

    if 'unsat' not in solution['solution'] and 'timeout' not in solution['solution']:
        # Only SAT results are saved in return_solutions
        valid_sat_subproblem_solutions.append(solution)
    elif not is_subproblem:
        timeout_or_unsat_complete_problem_solution = solution
    # if not is_subproblem:
    #     print(solution)
    return solution


def main():
    instances_dir = 'resources/instances/'
    synthesis_timeout = 3 * 60
    solvers = (SynthesisSolver.CVC5, SynthesisSolver.Rosette)

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        for solver in solvers:
            # Edit below to solve a specific instance:
            # if 'retry_until_example' not in filename:
            #     continue
            # if 'obj1f775d' not in filename:
            #     continue

            with open(filename, 'r') as f:
                synt_decls = json.load(f)
            instance_name = os.path.basename(filename).replace('.json', '')
            args.append((instance_name,
                         synt_decls,
                         solver,
                         synthesis_timeout,
                         False  # use_metadata
                         ))

    for arg in args:
        start_time = time.perf_counter()
        result = synthesize_data_transforms(*arg)
        if time.perf_counter() - start_time > synthesis_timeout + 5:
            print(f'WARNING: Took {human_time(time.perf_counter() - start_time)},'
                  f'which is longer than the timeout of {human_time(synthesis_timeout)}.')
        for r in result:
            print(f'{arg[2].name} solution for {arg[0]}::{r["name"]}: '
                  f'{r["solution"]}. '
                  f'Took {human_time((time.perf_counter() - start_time))}')


def make_table():
    rows = []
    for file in glob.glob('data_synthesis_solutions/*.json'):
        with open(file, 'r') as f:
            solutions = json.load(f)
        for sol in solutions:
            row = {'instance name': sol["instance"],
                   'function name': sol["name"],
                   'depth': sol["depth"],
                   'solver': sol['solver'],
                   'solution': sol["solution"],
                   'solve time': sol["solve time"]
                   }
            rows.append(row)

    rows = sorted(rows, key=lambda r: (r['instance name'], r['function name'], r['solver']))
    writer = csv.DictWriter(sys.stdout, fieldnames=rows[0].keys())
    writer.writeheader()
    writer.writerows(rows)


if __name__ == '__main__':
    main()
    make_table()
