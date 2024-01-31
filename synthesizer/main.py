import csv
import glob
import json
import os
import subprocess
import time

from synthesizer.data_transforms_synthesizer import synthesize_data_transforms
from synthesizer.util import human_time, SynthesisSolver


def main():
    instances_dir = 'resources/instances/'
    synthesis_timeout = 5 * 60
    solvers = (SynthesisSolver.CVC5, SynthesisSolver.Rosette)

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        for solver in solvers:
            # Edit below to solve a specific instance:
            # if 'retry_until_example' not in filename:
            #     continue
            # if 'synth_obj_12_35bb32' not in filename:
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
        assert len(result) > 0
        if time.perf_counter() - start_time > synthesis_timeout + 5:
            print(f'WARNING: Took {human_time(time.perf_counter() - start_time)},'
                  f'which is longer than the timeout of {human_time(synthesis_timeout)}.')
        for r in result:
            print(f'{arg[2].name} solution for {arg[0]}::{r["name"]}: '
                  f'{r["solution"]}. '
                  f'Took {human_time((time.perf_counter() - start_time))}')

        subprocess.run(['pkill', 'cvc5'])
        subprocess.run(['pkill', 'racket'])


def make_tables(results_table_filename: str, comparison_table_filename: str):
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
            solver_comparison_row[f'{solver} solution'] = sol["solution"]
            solver_comparison_row[f'{solver} solve time'] = sol["solve time"]
        solver_comparison_rows.append(solver_comparison_row)

    solver_comparison_rows = sorted(solver_comparison_rows,
                                    key=lambda r: (r['instance name'], r['function name']))
    with open(comparison_table_filename, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=solver_comparison_rows[0].keys())
        writer.writeheader()
        writer.writerows(solver_comparison_rows)


if __name__ == '__main__':
    main()
    make_tables('results.csv', 'solver_comparison.csv')
