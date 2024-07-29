import os
import subprocess
from collections import deque
from typing import Any

from synthesizer.encoder.arithmetic_to_cvc5 import get_arithmetic_start_symbol
from synthesizer.util import get_timeout_command_prefix, human_time, SyntDecl


class Arithmetic2RosetteEncoder:
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
(require (file "{os.getcwd()}/resources/synthesis/synthesis_arith_lang.rkt"))\n\n"""

    def build_general_rosette_grammar(self):
        s = f"""
(define-grammar (json-selector x)
  [SyntBool
    (choose
     (empty? x)
     (not (SyntBool))"""
        s += '\n    )'
        s += """
  ]
"""
        s += f"""
  [SyntInt (choose 
    (index x (SyntInt))
    (+ (SyntInt) (SyntInt))
    (* (SyntInt) (SyntInt))
    (abs (SyntInt))
    (?? integer?)
  )]"""
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

        return s

    def parse_rosette_output_aux(self, tokens: deque):
        two_arg_functions = ['child', 'index', 'descendant', 'syntEq', '*', '+']
        one_arg_functions = ['not', 'empty?', 'abs']
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

        try:
            return int(token)
        except ValueError:
            pass

        raise NotImplementedError(f'Handle parsing {token}')

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
            elif f_name == 'abs':
                a0 = f_args
                return f'|{self.rosette_to_jsonpath(a0)}|'
            elif f_name in ('+', '*', '==', '>=', '<=', '>', '<'):
                a0, a1 = f_args
                return f'({self.rosette_to_jsonpath(a0)} {f_name} {self.rosette_to_jsonpath(a1)})'
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

    def get_query(self, synt_decl: SyntDecl, depth: int):
        rosette_text = ''
        rosette_text += self.rosette_file_preamble()
        rosette_text += self.build_general_rosette_grammar()
        rosette_text += self.build_rosette_samples(synt_decl)
        start_symbol = get_arithmetic_start_symbol(synt_decl['constraints'])
        rosette_text += self.build_rosette_synthesis_query(synt_decl, depth, start_symbol)
        return rosette_text

    def run_command(self, racket_filename: str, timeout: int, depth: int) -> str:
        """
        Runs a pre-written Racket file and returns the solution, in our jsonpath format.
        :param racket_filename: The name of the file with the racket problem
        :param timeout: Synthesis timeout in seconds
        :return: solution in jsonpath format
        """
        racket_command = get_timeout_command_prefix(timeout) + ['racket', racket_filename]
        try:
            result = subprocess.run(racket_command, capture_output=True, text=True, timeout=timeout)

            if 'unsat' in result.stdout:
                if depth is None:
                    racket_out = '(unsat)'
                else:
                    racket_out = f'(unsat d={depth})'
            else:
                racket_out = "\n".join(result.stdout.split('\n')[1:])
                try:
                    racket_out = self.convert_rosette_to_jsonpath(racket_out)
                except Exception as e:
                    subprocess.run(['subl', racket_filename])
                    raise RuntimeError(
                        f'Something wrong with racket output to {" ".join(racket_command)}: {e}\n'
                        f'stdout: {result.stdout}\n'
                        f'stderr: {result.stderr}\n')
            if len(result.stderr) > 0:
                print('racket call stderr:', result.stderr)
            return racket_out

        except subprocess.TimeoutExpired:
            return f'(timeout {human_time(timeout)})'
