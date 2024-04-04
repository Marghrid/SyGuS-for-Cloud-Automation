import glob
import json
import os
import subprocess
import time

from synthesizer.data_transforms_synthesizer import synthesize_data_transforms
from synthesizer.util import human_time, SynthesisSolver


def main(instances_dir: str, synthesis_timeout: int):
    solvers = (SynthesisSolver.CVC5, SynthesisSolver.Rosette)
    # solvers = (SynthesisSolver.Rosette, )

    args = []
    for filename in glob.glob(f"{instances_dir}*.json"):
        for solver in solvers:
            # Edit below to solve a specific instance:
            # if 'retry_until_example' not in filename:
            #     continue
            # if 'StopInstancesCond_synth_obj585a2b' not in filename:
            #     continue
            # if solver.name == 'CVC5':
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

            # decls = 0
            # num_input_output_pairs = 0
            # for decl in synt_decls:
            #     decls += 1
            #     num_input_output_pairs += len(decl['constraints'])
    # print('On average, each decl has', num_input_output_pairs / decls, 'input-output pairs.')

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


if __name__ == '__main__':
    # instances_dir = 'resources/json_solver_benchmarks/'
    instances_dir = 'resources/hand_built/'
    synthesis_timeout = 5 * 60
    main(instances_dir, synthesis_timeout)
