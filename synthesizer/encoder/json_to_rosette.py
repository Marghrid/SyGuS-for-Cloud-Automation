import os
import signal
import subprocess
from collections import deque
from typing import Any

# noinspection PyUnresolvedReferences
from synthesizer.util import active_children, get_timeout_command_prefix, handler, human_time, SyntDecl


def get_json_start_symbol(ctrs: list[dict[str, Any]]) -> str:
    if all(isinstance(ctr["output"], bool) for ctr in ctrs):
        start_symb = 'syntBool'
    elif all(isinstance(ctr["output"], list) for ctr in ctrs) or \
            all(isinstance(ctr["output"], dict) for ctr in ctrs) or \
            all(isinstance(ctr["output"], int) for ctr in ctrs) or \
            all(isinstance(ctr["output"], str) for ctr in ctrs):
        start_symb = 'syntJ'
    else:
        raise NotImplementedError(f'Which start symbol for '
                                  f'{[ctr["output"].__class__.__name__ for ctr in ctrs]}')
    return start_symb


class Json2RosetteEncoder():
    def to_racket(self, i: Any):
        if isinstance(i, bool):
            return '#t' if i else '#f'
        if isinstance(i, str):
            return '"' + i.replace('"', '\\"') + '"'
        if isinstance(i, int) or isinstance(i, float):
            return str(i)
        if i is None:
            return "null"
        if isinstance(i, list):
            return f'(list {" ".join(map(self.to_racket, i))})'
        if isinstance(i, dict):
            # dict is a list of KV structs
            s = "(list "
            for k, v in i.items():
                s += f'(KV {self.to_racket(k)} {self.to_racket(v)}) '
                # s += f'({to_racket(k)} . {to_racket(v)}) '
            s += ")"
            return s

        raise NotImplementedError(f'to_racket not implemented for {i.__class__.__name__}')

    def rosette_file_preamble(self):
        return f"""#lang rosette
    
    (require racket/include)
    (require racket/dict)
    (require rosette/lib/synthax)
    (require (file "{os.getcwd()}/resources/synthesis/synthesis_json_lang.rkt"))\n\n"""

    def build_general_rosette_grammar(self, keys: list[str], indices: list[int], values: list[str]):
        if len(keys) == 1:
            # Rosette does not deal well with single element lists
            keys.append('fillerstr')
        keys_str = ' '.join(f'"{k}"' for k in keys)
        values_str = ' '.join(f'"{v}"' if isinstance(v, str) else f'{v}' for v in values)
        indices_str = ' '.join(map(str, indices))
        s = f"""
    (define-grammar (json-selector x)
      [syntBool
        (choose
         (empty? (syntJ))
         (not (syntBool))"""

        if len(values) > 0:
            s += '\n     (syntEq (syntJ) (syntVal))'

        s += '\n    )'
        s += """
      ]
      [syntJ
       (choose
        (index x (syntInt))
        (length (syntJ))"""
        if len(keys) > 0:
            s += f"""
        (child (syntJ) (syntK))
        (descendant (syntJ) (syntK))"""

        s += "\n    (index (syntJ) (syntInt))"
        if len(values) > 0:
            s += '\n(syntAdd (syntVal) (syntJ))'
        s += "\n   )]"

        if len(keys) > 0:
            s += f'\n  [syntK (choose {keys_str})]'

        s += f"\n  [syntInt (choose {indices_str})]"
        if len(values) > 0:
            s += f'\n  [syntVal (choose {values_str})]'
        s += '\n  )\n\n'
        return s

    def build_rosette_samples(self, synt_decl):
        s = ''
        for io_idx, io in enumerate(synt_decl['constraints']):
            s += f'(define sample{io_idx} {self.to_racket(io["inputs"])})\n'
        s += '\n'
        return s

    def build_rosette_synthesis_query(self, synt_decl, depth: int, start_symb: str):
        assert depth is not None
        asserts = []
        f_name = synt_decl["name"]
        for ctr_idx, ctr in enumerate(synt_decl["constraints"]):
            asserts.append(f'(assert (equal? ({f_name} sample{ctr_idx}) {self.to_racket(ctr["output"])}))')

        asserts_str = ('\n' + ' ' * 10).join(asserts)

        s = f"""
    (define ({f_name} x)
      (json-selector x {'#:depth ' + str(depth) if depth is not None else ''} #:start {start_symb})
    )
    """
        s += f"""
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

    def parse_rosette_output_aux(self, tokens: deque):
        two_arg_functions = ['child', 'index', 'descendant', 'syntEq']
        one_arg_functions = ['not', 'empty?']
        token = tokens.popleft()
        if token[0] == '(':
            func_name = token[1:]
            if func_name in one_arg_functions:
                arg0 = self.parse_rosette_output_aux(tokens)
                return func_name, arg0
            elif func_name in two_arg_functions:
                arg0 = self.parse_rosette_output_aux(tokens)
                arg1 = self.parse_rosette_output_aux(tokens)
                return func_name, (arg0, arg1)
            if func_name == 'choose':
                # ignore
                return self.parse_rosette_output_aux(tokens)
        if 'x' in token:
            return 'x'
        if token[-1] == ')':
            return eval(token.replace(')', ''))

        raise NotImplementedError(f'parse_rosette_output_aux does not handle {token}')

    def parse_rosette_output(self, rosette: str):
        tokens = deque(rosette.split())
        # token = tokens.popleft()
        token = tokens.popleft()
        assert token == '(define', f'removed {token} from {tokens}.'
        _ = tokens.popleft()  # func name
        _ = tokens.popleft()  # x

        return self.parse_rosette_output_aux(tokens)

    def rosette_to_jsonpath(self, ast):
        input_name = 'x'
        if isinstance(ast, tuple):
            f_name, f_args = ast

            if f_name == 'child':
                a0, a1 = f_args
                return f'{self.rosette_to_jsonpath(a0)}.{a1}'
            elif f_name == 'descendant':
                a0, a1 = f_args
                return f'{self.rosette_to_jsonpath(a0)}..{a1}'
            elif f_name == 'index':
                a0, a1 = f_args
                return f'{self.rosette_to_jsonpath(a0)}[{a1}]'
            elif f_name == 'syntEq':
                a0, a1 = f_args
                return f'({self.rosette_to_jsonpath(a0)} == {self.rosette_to_jsonpath(a1)})'
            elif f_name == 'not':
                a0 = f_args
                return f'! ({self.rosette_to_jsonpath(a0)})'
            elif f_name == 'empty?':
                a0 = f_args
                return f'(len({self.rosette_to_jsonpath(a0)}) == 0)'
            else:
                raise NotImplementedError(f'to_jsonpath not implemented for operation {f_name}.')
        elif ast == input_name:
            return '$'
        if isinstance(ast, str):
            return f'"{ast}"'
        else:
            return ast

    def convert_rosette_to_jsonpath(self, rosette: str):
        ast = self.parse_rosette_output(rosette)
        return self.rosette_to_jsonpath(ast)

    def get_query(self, synt_decl: SyntDecl, depth: int, indices: list[int], keys: list[str],
                  values: list[str]):
        rosette_text = ''
        rosette_text += self.rosette_file_preamble()
        rosette_text += self.build_general_rosette_grammar(keys, indices, values)
        rosette_text += self.build_rosette_samples(synt_decl)
        start_symbol = get_json_start_symbol(synt_decl['constraints'])
        rosette_text += self.build_rosette_synthesis_query(synt_decl, depth, start_symbol)
        return rosette_text

    def run_command(self, racket_filename: str, timeout: int, depth: int) -> str:
        """
        Runs a pre-written Racket file and returns the solution, in our jsonpath format.
        :param racket_filename: The name of the file with the racket problem
        :param timeout: Synthesis timeout in seconds
        :return: solution in jsonpath format
        """
        global active_children
        signal.signal(signal.SIGINT, handler)
        signal.signal(signal.SIGTERM, handler)
        racket_command = get_timeout_command_prefix(timeout) + ['racket', racket_filename]
        try:
            process = subprocess.Popen(racket_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            active_children.add(process.pid)
            stdout, stderr = process.communicate(timeout=timeout)
            active_children.discard(process.pid)
            if 'unsat' in stdout:
                if depth is None:
                    racket_out = '(unsat)'
                else:
                    racket_out = f'(unsat d={depth})'
            else:
                racket_out = "\n".join(stdout.split('\n')[1:])
                try:
                    racket_out = self.convert_rosette_to_jsonpath(racket_out)
                except Exception as e:
                    raise RuntimeError(
                        f'Something wrong with racket output to {" ".join(racket_command)}: {e}\n'
                        f'stdout: {stdout}\n'
                        f'stderr: {stderr}\n')
            if len(stderr) > 0:
                print('racket call stderr:', stderr)
            return racket_out

        except subprocess.TimeoutExpired:
            return f'(timeout {human_time(timeout)})'
