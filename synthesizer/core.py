import glob
import json
import multiprocessing.context
import multiprocessing.pool
import os.path
import re
import time

from synthesizer.to_rosette import build_rosette_grammar, build_rosette_samples, build_rosette_synthesis_query, \
    rosette_file_preamble, run_racket_command
from synthesizer.util import human_time

max_time = 20 * 60


def synthesize_data_transforms(instance_name, synt_decls):
    racket_dir = "resources/racket_programs/"
    solutions_dir = "synthesis_solutions/"
    solution = {}

    for synt_decl in sorted(synt_decls, key=lambda decl: int(re.fullmatch('_?f\??_(\d+)', decl['name'])[1])):
        rosette_text = ''
        rosette_text += rosette_file_preamble()

        rosette_text += build_rosette_grammar(synt_decl)
        rosette_text += build_rosette_samples(synt_decl)
        rosette_text += build_rosette_synthesis_query(synt_decl)

        func_name = synt_decl['name']
        solution[func_name] = {}

        racket_filename = os.path.join(racket_dir, f'{instance_name}{"" if func_name[0] == "_" else "_"}{func_name}.rkt')
        with open(racket_filename, 'w') as f:
            f.write(rosette_text)

        start_racket_call_time = time.perf_counter()
        with multiprocessing.pool.ThreadPool(processes=1) as pool:
            pool_result = pool.apply_async(run_racket_command, args=(racket_filename,))

            try:
                racket_out = pool_result.get(timeout=max_time)  # 20min
                racket_out = '\n'.join(racket_out.splitlines()[1:])
            except multiprocessing.context.TimeoutError as e:
                print(f'timeout {human_time(max_time)} {e}')
                racket_out = '(timeout)'
        print(racket_out)
        solution[func_name]["solution"] = racket_out
        solution[func_name]["solve time"] = time.perf_counter() - start_racket_call_time
        solution[func_name]["solve time (h)"] = human_time(time.perf_counter() - start_racket_call_time)
        print(f'Took {solution[func_name]["solve time (h)"]}')
        solution_filename = instance_name + '.json'
        with open(solutions_dir + solution_filename, 'w') as sol_file:
            json.dump(solution, sol_file, indent=2)
    return solution


def main():
    instances_dir = 'resources/instances/'
    # for filename in glob.glob(f"{instances_dir}*.pickle"):
    #     with open(filename, 'rb') as f:
    #         pickle_contents = pickle.load(f)
    #     synt_decls = {}
    #     for f_name in pickle_contents:
    #         synt_decls[f_name] = pickle_contents[f_name].constraints
    #     instance_name = os.path.basename(filename).replace('.pickle', '')
    #     synthesize_data_transforms(instance_name, synt_decls)

    for filename in glob.glob(f"{instances_dir}*.json"):
        if "506259" in filename:
            continue
        with open(filename, 'r') as f:
            synt_decls = json.load(f)
        instance_name = os.path.basename(filename).replace('.json', '')
        synthesize_data_transforms(instance_name, synt_decls)


if __name__ == '__main__':
    main()
