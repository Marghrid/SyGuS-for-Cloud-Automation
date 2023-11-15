import datetime
import glob
import hashlib
import json
import multiprocessing
import multiprocessing.dummy  # So it uses threads, not processes
import os.path
import subprocess
import time
from typing import Any

from synthesizer.to_rosette import build_general_rosette_grammar, build_rosette_samples, build_rosette_synthesis_query, \
    convert_rosette_to_jsonpath, get_racket_indices, get_racket_keys, get_racket_values, rosette_file_preamble
from synthesizer.util import human_time

valid_sat_subproblem_solutions = []  # Where each subproblem thread saves its positive solution


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
    :param use_metadata: Whether metadata should be used as input to the synthesis
    :return solution dictionary
    """
    global valid_sat_subproblem_solutions
    racket_dir = "resources/racket_programs/"
    solutions_dir = "data_synthesis_solutions/"
    all_solutions = []

    # The synthesis of each data transform is solved sequencially
    for synt_decl in sorted(synt_decls, key=lambda decl: decl['name']):

        # String values collected from the instances, because Rosette's strings are not solvable types.
        keys = sorted(get_racket_keys(synt_decl))
        indices = get_racket_indices(synt_decl)
        values = sorted(get_racket_values(synt_decl), key=lambda v: (isinstance(v, str), v))

        num_processes = multiprocessing.cpu_count() // 2

        # If there are many keys and/or values and we have more than one CPU,
        # we split the keys and values into subsets and make smaller subproblems.
        if (len(keys) > 15 or len(values) > 15) and num_processes > 1:
            # We split it, so we have (approximately) as many subproblems per depth as the computer has CPUs.
            total_keys_vals = len(keys) + len(values)
            list_size = max(1, int(total_keys_vals / max(1, num_processes - 1)))
            keys_sublists = [keys[i:i + list_size] for i in range(0, len(keys), list_size)]
            values_sublists = [values[i:i + list_size] for i in range(0, len(values), list_size)]

            # Some subproblems have only keys, others have only values
            keys_values = [(k, []) for k in keys_sublists] + \
                          [([], v) for v in values_sublists]
        else:
            keys_values = []  # no subproblems otherwise

        # Define all subproblems
        subproblems_args = [
            (synt_decl, indices, keys, values, depth, instance_name, racket_dir, synthesis_timeout, use_metadata, True) for
            keys, values in keys_values for depth in range(2, 6)]

        # Define whole main problem
        complete_problem_args = [
            (synt_decl, indices, keys, values, depth, instance_name, racket_dir, synthesis_timeout, use_metadata, False) for
            depth in range(2, 6)]

        valid_sat_subproblem_solutions = []  # clear list from previous runs

        # Start processes solving subproblems
        with multiprocessing.dummy.Pool(processes=num_processes - 1) as subproblems_pool:
            async_result_subproblems = subproblems_pool.starmap_async(
                write_and_solve_rosette_problem, subproblems_args)

            with multiprocessing.dummy.Pool(processes=1) as main_problem_pool:
                async_result_complete_problem = main_problem_pool.starmap_async(
                    write_and_solve_rosette_problem, complete_problem_args)

                start_time = time.perf_counter()

                # cycle that watches all threads:
                while time.perf_counter() - start_time < synthesis_timeout:
                    time.sleep(0.1)  # Check every 0.1 secs
                    if len(valid_sat_subproblem_solutions) > 0:
                        # One of the subproblems returned SAT
                        all_solutions.extend(valid_sat_subproblem_solutions)
                        break

                    elif async_result_complete_problem.ready():  # Even if it times out, it should be caught here.
                        # Complete problem finished (either successfully or not)
                        # Kill every thread:
                        all_solutions.extend(async_result_complete_problem.get())
                        break

                subproblems_pool.close()
                subproblems_pool.terminate()
                main_problem_pool.close()
                main_problem_pool.terminate()

                # Write all solutions to solutions file, even before it has not computed solutions for all functions.
                solution_filename = instance_name + '.json'
                if not os.path.isdir(solutions_dir):
                    os.makedirs(solutions_dir)
                with open(os.path.join(solutions_dir, solution_filename), 'w') as sol_file:
                    json.dump(all_solutions, sol_file, indent=2)

        subproblems_pool.close()
        subproblems_pool.terminate()
        main_problem_pool.close()
        main_problem_pool.terminate()

    return all_solutions


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
    global valid_sat_subproblem_solutions
    synt_decl, comment = preprocess(synt_decl, use_metadata)
    rosette_text = ''
    rosette_text += rosette_file_preamble()
    rosette_text += build_general_rosette_grammar(keys, indices, values)
    rosette_text += build_rosette_samples(synt_decl)
    rosette_text += build_rosette_synthesis_query(synt_decl, depth)
    func_name = synt_decl['name']
    racket_filename = get_racket_filename(depth, func_name, instance_name, racket_dir, keys, values)
    if not os.path.isdir(racket_dir):
        os.makedirs(racket_dir)
    with open(racket_filename, 'w') as f:
        f.write(rosette_text)
    start_racket_call_time = time.perf_counter()
    racket_out = run_racket_command(racket_filename, synthesis_timeout)
    elapsed = time.perf_counter() - start_racket_call_time
    solution = {'name': func_name,
                'solution': racket_out,
                'solve time': elapsed,
                'solve time (h)': human_time(elapsed),
                'keys': keys,
                'values': values,
                'depth': depth,
                'is subproblem': is_subproblem,
                'comment': comment}

    if 'unsat' not in solution['solution'] and 'timeout' not in solution['solution']:
        # Only SAT results are saved in return_solutions
        valid_sat_subproblem_solutions.append(solution)
    # print(len(keys), len(values), depth, solution)
    return solution


def main():
    instances_dir = 'resources/instances/'
    synthesis_timeout = 5 * 60

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        # To solve a specific instance:
        # if 'obj18a873' not in filename:
        #     continue
        with open(filename, 'r') as f:
            synt_decls = json.load(f)
        instance_name = os.path.basename(filename).replace('.json', '')
        args.append((instance_name,
                     synt_decls,
                     synthesis_timeout,
                     False  # use_metadata
                     ))

    for arg in args:
        start_time = time.perf_counter()
        results = synthesize_data_transforms(*arg)
        if time.perf_counter() - start_time > synthesis_timeout + 5:
            print(f'WARNING: Took {human_time(time.perf_counter() - start_time)},'
                  f'which is longer than the timeout of {human_time(synthesis_timeout)}.')
        for r in results:
            print(f'Solution for {arg[0]}::{r["name"]}: '
                  f'{r["solution"]}. '
                  f'Took {human_time((time.perf_counter() - start_time))}')


if __name__ == '__main__':
    main()
