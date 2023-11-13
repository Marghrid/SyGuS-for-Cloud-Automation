import datetime
import glob
import hashlib
import json
import multiprocessing
import os.path
import subprocess
import time
from typing import Any

from synthesizer.to_rosette import build_rosette_grammar, build_rosette_samples, build_rosette_synthesis_query, \
    convert_rosette_to_jsonpath, get_racket_indices, get_racket_keys, get_racket_values, rosette_file_preamble
from synthesizer.util import human_time


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


def get_racket_filename(depth: int, func_name: str, instance_name: str, racket_dir: str, keys: list[str],
                        values: list[str]) -> str:
    timestamp = get_timestamp()
    return os.path.join(
        racket_dir,
        f'{instance_name}{"" if func_name[0] == "_" else "_"}{func_name}_'
        f'{my_hash(str(keys) + str(values))}_{depth}_'
        f'{timestamp}.rkt')


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
    constraints = synt_decl['constraints']
    in_idx_to_remove = []
    for i in range(len(constraints[0]['inputs'])):
        if all(ctr['inputs'][i] == constraints[0]['inputs'][i] for ctr in constraints):
            in_idx_to_remove.append(i)
    for i in sorted(in_idx_to_remove, reverse=True):
        for ctr in synt_decl['constraints']:
            ctr['inputs'].pop(i)
    if len(in_idx_to_remove) > 0:
        comment += f'Removing inputs {in_idx_to_remove} because always the same.\n'

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


def run_racket_command(racket_filename: str, timeout: int) -> str:
    """
    Runs a pre-written Racket file and returns the solution, in our jsonpath format.
    :param racket_filename: The name of the file with the racket problem
    :param timeout: Synthesis timeout in seconds
    :return: solution in jsonpath format
    """
    racket_command = ['racket', racket_filename]
    try:
        result = subprocess.run(racket_command, capture_output=True, text=True, timeout=timeout)

        if 'unsat' in result.stdout:
            racket_out = '(unsat)'
        else:
            racket_out = "\n".join(result.stdout.split('\n')[1:])
            try:
                racket_out = convert_rosette_to_jsonpath(racket_out)
            except Exception as e:
                raise RuntimeError(f'Something wrong with racket output to {" ".join(racket_command)}:\n{result.stdout}\n{e}')
        if len(result.stderr) > 0:
            print('racket call stderr:', result.stderr)
        return racket_out

    except subprocess.TimeoutExpired:
        return f'(timeout {human_time(timeout)})'


def synthesize_data_transforms(instance_name: str,
                               synt_decls: list[dict[str:Any]],
                               synthesis_timeout: int,
                               use_metadata: bool = True) -> list[dict[str:Any]]:
    """
    Given synthesis function declarations, with a name and a list of constraints,
    synthesize a JSONPath expression for each undefined function.
    :param instance_name: The instance name, which will be used to name auxiliary racket file and solution file.
    :param synt_decls: Input read from the json file.
    :param synthesis_timeout: Max synthesis time in seconds.
    :param use_metadata: whether metadata should be used as input to the synthesis
    :return solution dictionary
    """
    racket_dir = "resources/racket_programs/"
    solutions_dir = "data_synthesis_solutions/"
    return_solutions = []
    all_solutions = []

    for synt_decl in sorted(synt_decls, key=lambda decl: decl['name']):

        keys = sorted(get_racket_keys(synt_decl))
        indices = get_racket_indices(synt_decl)

        values = sorted(get_racket_values(synt_decl), key=lambda v: (isinstance(v, str), v))

        if len(keys) > 30:
            # If there is a large number of keys, the problem gets split into many subproblems
            keys_sublists = [keys[i:i + 15] for i in range(0, len(keys), 15)]
        else:
            keys_sublists = [keys]

        if len(values) > 30:
            # If there is a large number of values, the problem gets split into many subproblems
            values_sublists = [values[i:i + 15] for i in range(0, len(values), 15)]
        else:
            values_sublists = [values]

        keys_values = [(k, []) for k in keys_sublists] + \
                      [([], v) for v in values_sublists]  # Some subproblems have only keys, others have only values

        num_processes = multiprocessing.cpu_count() // 2
        number_of_calls_per_iteration = max(1, int(1 + len(keys_values) / num_processes))
        num_iterations = 4
        num_calls = number_of_calls_per_iteration * num_iterations + 1  # final call
        timeout = synthesis_timeout // num_calls

        solved = False
        for depth in range(2, 6):
            if solved:
                break
            keys_values_solutions = []

            args = [(synt_decl, indices, keys, values, depth, instance_name, racket_dir, timeout, use_metadata, True) for
                    keys, values in keys_values]
            with multiprocessing.Pool(processes=num_processes) as pool:
                keys_values_solutions = pool.starmap(write_and_solve_rosette_problem, args)
            # print(solution)
            all_solutions.extend(keys_values_solutions)

            # Write all solutions to solutions file, even if it has not computed solutions for all functions.
            solution_filename = instance_name + '.json'
            if not os.path.isdir(solutions_dir):
                os.makedirs(solutions_dir)
            with open(os.path.join(solutions_dir, solution_filename), 'w') as sol_file:
                json.dump(all_solutions, sol_file, indent=2)

                for solution in keys_values_solutions:
                    if 'unsat' not in solution['solution'] and 'timeout' not in solution['solution']:
                        # Only SAT results are saved in return_solutions
                        solved = True
                        return_solutions.append(solution)

        # After trying to solve the subproblems, if none is solved, try to solve the complete problem:
        if not solved:
            solution = write_and_solve_rosette_problem(synt_decl, indices, keys, values, 6, instance_name,
                                                       racket_dir, timeout, use_metadata, False)
            # print(solution)
            all_solutions.append(solution)

            # Write all solutions to solutions file, even if it has not computed solutions for all functions.
            solution_filename = instance_name + '.json'
            if not os.path.isdir(solutions_dir):
                os.makedirs(solutions_dir)
            with open(os.path.join(solutions_dir, solution_filename), 'w') as sol_file:
                json.dump(all_solutions, sol_file, indent=2)

            return_solutions.append(solution)

    return return_solutions


def write_and_solve_rosette_problem(synt_decl, indices: list[int], keys: list[str], values: list[str],
                                    depth: int, instance_name: str, racket_dir: str, synthesis_timeout: int,
                                    use_metadata: bool, is_subproblem):
    """
    Auxiliary function that, given information about a synthesis instance, writes a Rosette synthesis query in Racket
    to a file and solves it.
    :param synt_decl: The synthesis problem, read from the instance file.
    :param indices: The constant values that should be considered for SyntInt.
    :param keys: The strings that should be considered for SyntK.
    :param values: The strings that should be considered for SyntVal.
    :param depth: The maximum depth of the synthesized program.
    :param instance_name: The instance name.
    :param racket_dir: The directory where the Racket file is stored
    :param synthesis_timeout: Synthesis timeout in seconds
    :param use_metadata: Whether metadata fields should be used for synthesis.
    :param is_subproblem: Whether this is a subproblem for a bigger synthesis problem.
    :return:
    """
    synt_decl, comment = preprocess(synt_decl, use_metadata)
    rosette_text = ''
    rosette_text += rosette_file_preamble()
    rosette_text += build_rosette_grammar(keys, indices, values)
    rosette_text += build_rosette_samples(synt_decl)
    rosette_text += build_rosette_synthesis_query(synt_decl, depth)
    func_name = synt_decl['name']
    racket_filename = get_racket_filename(depth, func_name, instance_name, racket_dir, keys, values)
    if not os.path.isdir(racket_dir):
        os.makedirs(racket_dir)
    with open(racket_filename, 'w') as f:
        f.write(rosette_text)
    # Using a ThreadPool to impose a timeout on Racket.
    start_racket_call_time = time.perf_counter()
    racket_out = run_racket_command(racket_filename, synthesis_timeout)
    elapsed = time.perf_counter() - start_racket_call_time
    solution = {'name': func_name,
                'solution': racket_out,
                'solve time': elapsed,
                'solve time (h)': human_time(elapsed),
                'is subproblem': is_subproblem,
                'comment': comment}

    # print(solution)
    return solution


def main():
    instances_dir = 'resources/instances/'
    synthesis_timeout = 5 * 60

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        # To solve a specific instance:
        # if '9830' not in filename:
        #     continue
        with open(filename, 'r') as f:
            synt_decls = json.load(f)
        instance_name = os.path.basename(filename).replace('.json', '')
        args.append((instance_name, synt_decls, synthesis_timeout, True))  # timeout of 5 minutes

    # To disable multiprocessing uncomment the following 3 lines:
    for arg in args:
        start_time = time.perf_counter()
        result = synthesize_data_transforms(*arg)
        print("Took", human_time(time.perf_counter() - start_time))
        if time.perf_counter() - start_time > synthesis_timeout:
            print(f'WARNING: Took {human_time(time.perf_counter() - start_time)},'
                  f'which is longer than the timeout of {human_time(synthesis_timeout)}.')
        # for r in result:
        #     print(f'Solution for {arg[0]}::{r["name"]} : {r["solution"]}')


if __name__ == '__main__':
    main()
