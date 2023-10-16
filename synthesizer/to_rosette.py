import subprocess
from typing import Any


def to_racket(i: Any):
    if isinstance(i, bool):
        return '#t' if i else '#f'
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
    if i is None:
        return set()
    if isinstance(i, str):
        return set()
    if isinstance(i, int):
        return set()
    if isinstance(i, list):
        return set().union(*(get_racket_keys_aux(e) for e in i))
    if isinstance(i, dict):
        return set(i.keys()).union(*(get_racket_keys_aux(v) for v in i.values()))

    raise NotImplementedError(f'get_racket_keys_aux not implemented for {i.__class__.__name__}')


def get_racket_values_aux(i: Any) -> set[Any]:
    if i is None:
        return set()
    if isinstance(i, bool):
        return set()
    if isinstance(i, str):
        return {i}
    if isinstance(i, int):
        return {i}
    if isinstance(i, list):
        return set().union(*(get_racket_values_aux(e) for e in i))
    if isinstance(i, dict):
        return set().union(*(get_racket_values_aux(v) for v in i.values()))

    raise NotImplementedError(f'get_racket_values_aux not implemented for {i.__class__.__name__}')


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


def get_racket_keys(synt_decl: dict[str:Any]) -> set[str]:
    keys = set()
    for ctr in synt_decl['constraints']:
        keys.update(get_racket_keys_aux(ctr['inputs']))

    return keys


def get_racket_values(synt_decl) -> set[str]:
    values = set()
    for ctr in synt_decl['constraints']:
        values.update(get_racket_values_aux(ctr['inputs']))

    return values


def get_racket_indices(synt_decl: dict[str:Any]) -> list[int]:
    current_max = 2  # Ensures there are at least 2 values for indices
    for ctr in synt_decl['constraints']:
        n = get_racket_max_list_index(ctr['inputs'])
        if n > current_max:
            current_max = n
    return list(range(current_max))


def rosette_file_preamble():
    return """#lang rosette
    
(require racket/include)
(require racket/dict)
(require rosette/lib/synthax)
(require "synthesis_lang.rkt")\n\n"""


def build_rosette_grammar(synt_decl):
    keys = ' '.join(f'"{k}"' for k in sorted(get_racket_keys(synt_decl)))
    indices = ' '.join(map(str, get_racket_indices(synt_decl)))
    values = ' '.join(f'"{v}"' if isinstance(v, str)
                      else f'{v}' for v in sorted(get_racket_values(synt_decl),
                                                  key=lambda v: (isinstance(v, str), v)))

    s = f"""
(define-grammar (json-selector x)
  [syntBool
  (choose
   (syntEq (syntJ) (syntV))
  )]
  [syntJ
   (choose
    x"""
    if len(keys) > 0:
        s += f"""
    (child (syntJ) (syntK))
    (descendant (syntJ) (syntK))"""

    s += """
    (index (syntJ) (syntI))
    (syntAdd (syntV) (syntJ))
    )]"""

    if len(keys) > 0:
        s += f'\n  [syntK (choose {keys})]'

    s += f"""
  [syntI (choose {indices})]
  [syntV (choose {values})]
  )
\n
"""
    return s


def build_rosette_samples(synt_decl):
    s = ''
    for io_idx, io in enumerate(synt_decl['constraints']):
        s += f'(define sample{io_idx} {to_racket(io["inputs"])})\n'
    s += '\n'
    return s


def build_rosette_synthesis_query(synt_decl):
    depth = 4
    asserts = []
    f_name = synt_decl["name"]
    for ctr_idx, ctr in enumerate(synt_decl["constraints"]):
        asserts.append(f'(assert (equal? ({f_name} sample{ctr_idx}) {to_racket(ctr["output"])}))')

    asserts_str = ('\n' + ' ' * 10).join(asserts)
    if all(isinstance(ctr["output"], bool) for ctr in synt_decl["constraints"]):
        start_symb = 'syntBool'
    elif all(isinstance(ctr["output"], list) for ctr in synt_decl["constraints"]) or \
            all(isinstance(ctr["output"], dict) for ctr in synt_decl["constraints"]) or \
            all(isinstance(ctr["output"], str) for ctr in synt_decl["constraints"]):
        start_symb = 'syntJ'
    else:
        raise NotImplementedError(f'Which startSymbol for '
                                  f'{[ctr["output"].__class__.__name__ for ctr in synt_decl["constraints"]]}')

    s = f"""
 (define ({f_name} x)
   (json-selector x #:depth {depth} #:start {start_symb})
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

    #     s += f"""
    # (define ({f_name} x)
    #        (syntEq (child (child (index x 1) "InstanceState") "Name") "stopped")
    # )
    # """
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


def to_python(arg):
    try:
        return eval(arg)
    except (NameError, SyntaxError) as e:
        try:
            return eval(arg.replace('true', 'True').replace('false', 'False'))
        except (NameError, SyntaxError) as e:
            return arg
