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


def make_table(table_filename: str):
    rows = []
    for file in glob.glob('data_synthesis_solutions/*.json'):
        with open(file, 'r') as f:
            solutions = json.load(f)
        for sol in solutions:
            assert sol is not None, file
            row = {'instance name': sol["instance"],
                   'function name': sol["name"],
                   'depth': sol["depth"],
                   'solver': sol['solver'],
                   'solution': sol["solution"],
                   'solve time': sol["solve time"]
                   }
            rows.append(row)

    for row in rows:
        if row['solver'] == SynthesisSolver.Rosette.name:
            if len(tuple(filter(lambda r: r['instance name'] == row['instance name'] and
                                          r['function name'] == row['function name'] and
                                          r['solver'] == SynthesisSolver.CVC5.name,
                                rows))) == 0:
                print(f'Instance {row["instance name"]}::{row["function name"]} not solved with CVC5.')
        elif row['solver'] == SynthesisSolver.CVC5.name:
            if len(tuple(filter(lambda r: r['instance name'] == row['instance name'] and
                                          r['function name'] == row['function name'] and
                                          r['solver'] == SynthesisSolver.Rosette.name,
                                rows))) == 0:
                print(f'Instance {row["instance name"]}::{row["function name"]} not solved with Rosette.')

    rows = sorted(rows, key=lambda r: (r['instance name'], r['function name'], r['solver']))
    with open(table_filename, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)


if __name__ == '__main__':
    main()
    make_table('results.csv')
