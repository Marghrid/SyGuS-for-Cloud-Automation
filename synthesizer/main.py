import glob
import json
import os
import time

from synthesizer.data_transforms_synthesizer import synthesize_data_transforms
from synthesizer.util import human_time, SynthesisSolver


def main(instances_dir: str, synthesis_timeout: int):
    solvers = (SynthesisSolver.CVC5, SynthesisSolver.Rosette)
    # solvers = (SynthesisSolver.CVC5,)
    # solvers = (SynthesisSolver.Rosette,)

    synthesis_problems = []
    if len(glob.glob(f"{instances_dir}*.json")) == 0:
        raise RuntimeError(f'No instances found in {instances_dir}*.json')
    for filename in sorted(glob.glob(f"{instances_dir}*.json")):
        for solver in solvers:
            print(f'Solving {filename} with {solver.name}')
            with open(filename, 'r') as f:
                synt_decls = json.load(f)
            instance_name = os.path.basename(filename).replace('.json', '')
            synthesis_problems.append(
                (instance_name, synt_decls, solver, synthesis_timeout,
                 False, False))  # use_metadata, use_ite

    for synthesis_problem in synthesis_problems:
        start_time = time.perf_counter()
        results = synthesize_data_transforms(*synthesis_problem)
        if len(results) == 0:
            print(f'[WARNING] No {synthesis_problem[2].name} solutions for {synthesis_problem[0]}.')
        if time.perf_counter() - start_time > synthesis_timeout + 5:
            print(f'[WARNING] Took {human_time(time.perf_counter() - start_time)},'
                  f'which is longer than the timeout of {human_time(synthesis_timeout)}.')
        for r in results:
            if r is None:
                print(f'{synthesis_problem[2].name} output None solution for {synthesis_problem[0]}.')
            print(f'{synthesis_problem[2].name} solution for {synthesis_problem[0]}::{r["name"]}: '
                  f'{r["solution"]}. '
                  f'Took {human_time((time.perf_counter() - start_time))}')


if __name__ == '__main__':
    # instances_dir = 'resources/json_solver_benchmarks/'
    # instances_dir = 'resources/hand_built/'
    # instances_dir = 'resources/arithmetic/'
    # instances_dir = 'resources/sample'
    instances_dir = 'resources/*/'
    synthesis_timeout = 5 * 60
    main(instances_dir, synthesis_timeout)
