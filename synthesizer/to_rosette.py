import multiprocessing.pool
import pickle
import subprocess
import time
from typing import Any

from synthesizer.util import human_time


def to_racket(i: Any):
    if isinstance(i, str):
        return f'"{i}"'
    if isinstance(i, int):
        return str(i)
    if isinstance(i, list):
        return f'(list {" ".join(map(to_racket, i))})'
    if isinstance(i, dict):
        # dict is a list of pairs
        s = "(list "
        for k, v in i.items():
            s += f'(cons {to_racket(k)} {to_racket(v)}) '
            # s += f'({to_racket(k)} . {to_racket(v)}) '
        s += ")"
        return s

    raise NotImplementedError(f'to_racket not implemented for {i.__class__.__name__}')


def get_racket_keys_aux(i: Any) -> set[str]:
    if isinstance(i, str):
        return set()
    if isinstance(i, int):
        return set()
    if isinstance(i, list):
        return set().union(*(get_racket_keys_aux(e) for e in i))
    if isinstance(i, dict):
        return set(i.keys()).union(*(get_racket_keys_aux(v) for v in i.values()))

    raise NotImplementedError(f'to_racket not implemented for {i.__class__.__name__}')


def get_racket_max_list_index(i: Any) -> int:
    if isinstance(i, str):
        return 0
    if isinstance(i, int):
        return 0
    if isinstance(i, list):
        return max([len(i)] + [get_racket_max_list_index(e) for e in i])
    if isinstance(i, dict):
        return max([get_racket_max_list_index(e) for e in i.values()])

    raise NotImplementedError(f'to_racket not implemented for {i.__class__.__name__}')


def get_racket_keys(synth_ctrs: list[tuple[Any, Any]]) -> set[str]:
    keys = set()
    for io in synth_ctrs:
        keys.update(get_racket_keys_aux(io[0]))

    return keys


def get_racket_indices(synth_ctrs: list[tuple[Any, Any]]) -> list[int]:
    current_max = 2  # Ensures there are at least 2 values for indices
    for io in synth_ctrs:
        n = get_racket_max_list_index(io[0])
        if n > current_max:
            current_max = n
    return list(range(current_max))


def rosette_file_preamble():
    return """#lang rosette
    
(require racket/include)
(require racket/dict)
(require rosette/lib/synthax)
(require "synthesis_lang.rkt")\n\n"""


def build_rosette_grammar(synth_ctrs):
    keys = ' '.join(f'"{k}"' for k in get_racket_keys(synth_ctrs))
    indices = ' '.join(map(str, get_racket_indices(synth_ctrs)))

    return f"""
(define-grammar (json-selector x)
  [syntJ
   (choose
    x
    (child (syntJ) (syntK))
    (index (syntJ) (syntI))
    ; (descendant (syntJ) (syntK))
    )]
  [syntK (choose {keys})]
  [syntI (choose {indices})]
  )\n
"""


def build_rosette_samples(synth_ctrs):
    s = ''
    for io_idx, io in enumerate(synth_ctrs):
        s += f'(define sample{io_idx} {to_racket(io[0])})\n'
    s += '\n'
    return s


def build_rosette_synthesis_query(f_name: str, synth_ctrs: list[tuple]):
    depth = 5
    asserts = []
    for io_idx, io in enumerate(synth_ctrs):
        asserts.append(f'(assert (eq? ({f_name} sample{io_idx}) "{io[1]}"))')

    asserts_str = ('\n' + ' ' * 10).join(asserts)
    s = f"""(define ({f_name} x)
  (json-selector x #:depth {depth} #:start syntJ)
  )

(define sol
  (synthesize
   #:forall (list)
   #:guarantee
   (begin {asserts_str}
          )))

(if (sat? sol)
    (print-forms sol) ; prints solution
    (println "unsat"))\n"""
    return s


def run_racket_command(racket_filename: str) -> str:
    racket_command = ['racket', racket_filename]
    print(f'Running "{" ".join(racket_command)}"...')
    result = subprocess.run(
        racket_command,
        capture_output=True,  # Python >= 3.7 only
        text=True  # Python >= 3.7 only
    )

    # print(result.stdout)
    print(result.stderr)
    return result.stdout


def main():
    with open('program.pickle', 'rb') as f:
        synt_decls = pickle.load(f)

    rosette_text = ''
    rosette_text += rosette_file_preamble()
    for s in synt_decls:
        synth_ctrs_evals = []
        for io in synt_decls[s].constraints:
            io = (list(map(eval, io[0])), io[1])
            synth_ctrs_evals.append(io)

        # FIXME CHEAT: select the right input
        synth_ctrs = []
        for io in synth_ctrs_evals:
            # io = ([io[0][3]], io[1])
            io = (io[0][3], io[0][3]['InstanceStatuses'][0]['InstanceState']['Name'])
            synth_ctrs.append(io)

        rosette_text += build_rosette_grammar(synth_ctrs)
        rosette_text += build_rosette_samples(synth_ctrs)
        rosette_text += build_rosette_synthesis_query(s, synth_ctrs)

        racket_filename = 'synthesis_example3.rkt'
        with open(racket_filename, 'w') as f:
            f.write(rosette_text)

        start_racket_call_time = time.perf_counter()
        with multiprocessing.pool.ThreadPool(processes=1) as pool:
            pool_result = pool.apply_async(run_racket_command, args=(racket_filename,))

            try:
                racket_out = pool_result.get(timeout=10 * 60)  # 10min
            except multiprocessing.context.TimeoutError as e:
                print(f'timeout {e}')
                racket_out = ''
        print(racket_out)
        print(f'Took {human_time(time.perf_counter() - start_racket_call_time)}')


if __name__ == '__main__':
    main()
