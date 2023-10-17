import glob
import json
import os.path
import subprocess
import time
from typing import Any

from synthesizer.to_rosette import build_rosette_grammar, build_rosette_samples, build_rosette_synthesis_query, \
    convert_rosette_to_jsonpath, rosette_file_preamble
from synthesizer.util import human_time


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
                raise RuntimeError(f'Something wrong with racket output to {" ".join(racket_command)}:\n{result.stdout}')
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
    solutions = []

    for synt_decl in sorted(synt_decls, key=lambda decl: decl['name']):
        synt_decl, comment = preprocess(synt_decl, use_metadata)

        rosette_text = ''
        rosette_text += rosette_file_preamble()

        rosette_text += build_rosette_grammar(synt_decl)
        rosette_text += build_rosette_samples(synt_decl)
        rosette_text += build_rosette_synthesis_query(synt_decl)

        func_name = synt_decl['name']
        solution = {'name': func_name}

        racket_filename = os.path.join(racket_dir, f'{instance_name}{"" if func_name[0] == "_" else "_"}{func_name}.rkt')
        if not os.path.isdir(racket_dir):
            os.makedirs(racket_dir)
        with open(racket_filename, 'w') as f:
            f.write(rosette_text)

        # Using a ThreadPool to impose a timeout on Racket.
        start_racket_call_time = time.perf_counter()
        racket_out = run_racket_command(racket_filename, synthesis_timeout)

        elapsed = time.perf_counter() - start_racket_call_time
        solution['solution'] = racket_out
        solution['solve time'] = elapsed
        solution['solve time (h)'] = human_time(elapsed)
        solution['comment'] = comment
        solutions.append(solution)

        # Write to solutions file, even if it has not computed solutions for all functions.
        solution_filename = instance_name + '.json'
        if not os.path.isdir(solutions_dir):
            os.makedirs(solutions_dir)
        with open(os.path.join(solutions_dir, solution_filename), 'w') as sol_file:
            json.dump(solutions, sol_file, indent=2)
    return solutions


def main():
    instances_dir = 'resources/instances/'

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        with open(filename, 'r') as f:
            synt_decls = json.load(f)
        instance_name = os.path.basename(filename).replace('.json', '')
        args.append((instance_name, synt_decls, 5 * 60, False))  # timeout of 5 minutes

    # To disable multiprocessing, comment the following 4 lines
    # with multiprocessing.Pool() as p:
    #     results = p.starmap(synthesize_data_transforms, args)
    # for i in range(len(results)):
    #     for r in results[i]:
    #         print(f'Solution for {args[i][0]}::{r["name"]} : {r["solution"]}')

    # To disable multiprocessing uncomment the following 3 lines:
    for arg in args:
        result = synthesize_data_transforms(*arg)
        for r in result:
            print(f'Solution for {arg[0]}::{r["name"]} : {r["solution"]}')


if __name__ == '__main__':
    main()
