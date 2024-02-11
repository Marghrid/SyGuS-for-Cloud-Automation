import csv
import glob
import json
import os
import re
import subprocess
import time

from synthesizer.data_transforms_synthesizer import synthesize_data_transforms
from synthesizer.util import human_time, SynthesisSolver


def main(instances_dir: str, synthesis_timeout: int):
    solvers = (SynthesisSolver.CVC5, SynthesisSolver.Rosette)

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        for solver in solvers:
            # Edit below to solve a specific instance:
            # if 'retry_until_example' not in filename:
            #     continue
            # if 'StopInstancesCond_synth_obj585a2b' not in filename:
            #     continue
            # if solver.name == 'Rosette':
            #     continue
            print(f'Solving {filename} with {solver.name}')
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
        results = synthesize_data_transforms(*arg)
        if len(results) == 0:
            print(f'[WARNING] No {arg[2].name} solutions for {arg[0]}.')
        if time.perf_counter() - start_time > synthesis_timeout + 5:
            print(f'[WARNING] Took {human_time(time.perf_counter() - start_time)},'
                  f'which is longer than the timeout of {human_time(synthesis_timeout)}.')
        for r in results:
            if r is None:
                print(f'{arg[2].name} output None solution for {arg[0]}.')
            print(f'{arg[2].name} solution for {arg[0]}::{r["name"]}: '
                  f'{r["solution"]}. '
                  f'Took {human_time((time.perf_counter() - start_time))}')

        subprocess.run(['pkill', 'cvc5'])
        subprocess.run(['pkill', 'racket'])


def make_csv_tables(results_table_filename: str, comparison_table_filename: str):
    results_rows = []
    for file in glob.glob('data_synthesis_solutions/*.json'):
        with open(file, 'r') as f:
            solutions = json.load(f)
        for sol in solutions:
            assert sol is not None, file
            row = {
                'instance name': sol["instance"],
                'function name': sol["name"],
                'depth': sol["depth"],
                'solver': sol['solver'],
                'solution': sol["solution"],
                'solve time': sol["solve time"]
            }
            results_rows.append(row)

    results_rows = sorted(results_rows, key=lambda r: (r['instance name'], r['function name'], r['solver']))
    with open(results_table_filename, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=results_rows[0].keys())
        writer.writeheader()
        writer.writerows(results_rows)

    instances = set((row['instance name'], row['function name']) for row in results_rows)
    solver_comparison_rows = []
    for instance in instances:
        solver_comparison_row = {'instance name': instance[0], 'function name': instance[1]}
        is_sat = False
        is_unsat = False
        for solver in map(lambda s: s.name, SynthesisSolver):
            instance_solver_solutions = tuple(
                filter(lambda r: r['instance name'] == instance[0] and
                                 r['function name'] == instance[1] and
                                 r['solver'] == solver,
                       results_rows))
            if len(instance_solver_solutions) == 1:
                sol = instance_solver_solutions[0]
            elif len(instance_solver_solutions) > 1:
                sol = min(instance_solver_solutions,
                          key=lambda s: float(s['solve time']))
            else:
                sol = {'solution': '-', 'solve time': '-'}

            if 'unsat' in sol['solution']:
                is_unsat = True
            elif sol['solution'] != '-' and 'timeout' not in sol['solution']:
                is_sat = True
            if is_sat and is_unsat:
                print(f'Warning: {instance[0]}::{instance[1]} is both sat and unsat.')
            solver_comparison_row[f'{solver} solution'] = sol["solution"]
            solver_comparison_row[f'{solver} solve time'] = sol["solve time"]
        solver_comparison_rows.append(solver_comparison_row)

    solver_comparison_rows = sorted(solver_comparison_rows,
                                    key=lambda r: (r['instance name'], r['function name']))
    with open(comparison_table_filename, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=solver_comparison_rows[0].keys())
        writer.writeheader()
        writer.writerows(solver_comparison_rows)


def to_latex(s: str) -> str:
    r = s.replace('_', '\\_').replace('$', '\\$').replace('#', '\\#').replace('%', '\\%')
    return r


def make_latex_tables():
    results_rows = []
    for file in glob.glob('data_synthesis_solutions/*.json'):
        with open(file, 'r') as f:
            solutions = json.load(f)
        for sol in solutions:
            assert sol is not None, file
            row = {
                'instance name': sol["instance"],
                'function name': sol["name"],
                'depth': sol["depth"],
                'solver': sol['solver'],
                'solution': sol["solution"],
                'solve time': sol["solve time"]
            }
            results_rows.append(row)

    results_rows = sorted(results_rows, key=lambda r: (r['instance name'], r['function name'], r['solver']))

    instances_dict = {}
    for result in results_rows:
        instance_name = f'{result["instance name"]}::{result["function name"]}'

        if instance_name not in instances_dict:
            instances_dict[instance_name] = result['solution']
        else:
            if 'timeout' in instances_dict[instance_name]:
                # One of the unsats does not have a depth, keep that one
                instances_dict[instance_name] = result['solution']
            elif ('unsat' in instances_dict[instance_name] and
                  'unsat' in result['solution']):
                # Both are UNSAT, keep the most general UNSAT
                if instances_dict[instance_name] == '(unsat)' or result['solution'] == '(unsat)':
                    instances_dict[instance_name] = '(unsat)'
                else:
                    depth_old = int(re.fullmatch(r'\(unsat d=(\d+)\)', instances_dict[instance_name]).groups()[0])
                    depth_new = int(re.fullmatch(r'\(unsat d=(\d+)\)', result['solution']).groups()[0])
                    if depth_new > depth_old:
                        instances_dict[instance_name] = result['solution']

            elif ('unsat' not in result['solution'] and
                  'timeout' not in result['solution']
                  and instances_dict[instance_name] != result['solution']):
                print(f'Warning: {instance_name} has different solutions: '
                      f'{instances_dict[instance_name]} and {result["solution"]}')
                if len(result["solution"]) < len(instances_dict[instance_name]) or \
                        (len(result["solution"]) == len(instances_dict[instance_name]) and
                         result["solution"] < instances_dict[instance_name]):
                    instances_dict[instance_name] = result['solution']

    print(r'''\begin{table*}[]
\centering
\begin{tabular}{@{}llrr@{}}''')
    print(r'Instance & synthesized function \\\hline')
    for instance in sorted(instances_dict, key=instances_dict.get):
        # if instances_dict[instance] == '--':
        #     continue
        l = fr'\texttt{{{to_latex(instance)}}} & \texttt{{{to_latex(instances_dict[instance])}}} \\'
        print(l)

    print(r'''\end{tabular}
\caption{Synthesis instances. In grey shading the ones that CVC5 did not solve.}
\label{tab:my-table}
\end{table*}''')


if __name__ == '__main__':
    # instances_dir = 'resources/json_solver_benchmarks/'
    instances_dir = 'resources/benchmarks_pt1/'
    synthesis_timeout = 5 * 60
    # main(instances_dir, synthesis_timeout)
    # instances_dir_name = instances_dir.replace('resources', '').replace('/', '')
    # make_csv_tables(f'results_{instances_dir_name}.csv', f'solver_comparison_{instances_dir_name}.csv')
    make_latex_tables()
